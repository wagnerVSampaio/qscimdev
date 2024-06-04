// =================================================================================
// File:    scimgateway.js
//
// Author:  Jarle Elshaug
//
// Purpose: Started by endpoint plugin
//          Listens and replies on incoming SCIM requests
//          Communicates with plugin using event callback
// =================================================================================

'use strict'

const http = require('http')
const jsonata = require('jsonata')
const https = require('https')
const Koa = require('koa')
const cors = require('koa-cors')
const Router = require('koa-router')
const bodyParser = require('koa-bodyparser')
const jwt = require('jsonwebtoken')
const passport = require('passport')
const OIDCBearerStrategy = require('passport-azure-ad').BearerStrategy
const dot = require('dot-object')
const nodemailer = require('nodemailer')
const fs = require('fs')
const path = require('path')
const callsite = require('callsite')
const utils = require('../lib/utils')
const countries = require('../lib/countries')
const { createChecker } = require('is-in-subnet')
const { createTerminus } = require('@godaddy/terminus')
require('events').EventEmitter.prototype._maxListeners = Infinity
const { fetchInterceptors } = require('./interceptors/functions')
const { fetchNotification } = require('./adapters/functions/notifications')
const { cache } = require('./adapters/functions/cache')
const { useListeners } = require('./listeners')
require('dotenv')

const { tracingConfig } = require("./tracing/config");


let span;
let requestSpan;

let caches = cache()


/**
 * @constructor
 */
const ScimGateway = function () {
  const startTime = utils.timestamp()
  const stack = callsite()
  const requester = stack[1].getFileName()
  const pluginName = path.basename(requester, '.js')
  const configDir = path.join(path.dirname(requester), '..', 'config')
  const configFile = path.join(`${configDir}`, `${pluginName}.json`) // config name prefix same as pluging name prefix
  let config = require(configFile).scimgateway
  let extConfigErr
  try {
    config = ScimGateway.prototype.processExtConfig(pluginName, config, true) // external config support process.env and process.file
  } catch (err) { extConfigErr = err }

  const gwName = path.basename(__filename, '.js') // prefix of current file
  const logDir = path.join(path.dirname(requester), '..', 'logs')
  const Log = require('../lib/logger').Log
  const log = new Log(utils.extendObj(utils.copyObj(config.log), { category: pluginName, colorize: process.stdout.isTTY || false, loglevel: { file: (!config.log.loglevel.file || config.log.loglevel.file === 'off') ? null : 'debug', console: 'debug' } }), path.join(`${logDir}`, `${pluginName}.log`))
  const logger = log.logger()
  this.logger = logger // exposed to plugin
  this.notValidAttributes = notValidAttributes // exposed to plugin
  this.authPassThroughAllowed = false // set to true by plugin if allowed
  let pwErrCount = 0
  let requestCounter = 0
  const oAuthTokenExpire = 3600 // seconds
  let isMailLock = false
  let ipAllowListChecker
  let scimDef
  let multiValueTypes
  let server

  let api;
let tracer
let verifyTracing = (ctx, name) => null
let endSpan = () => null
try{
  if(tracingConfig.enabled){
    api = require('@opentelemetry/api')
    const tracingFunctions = require('./tracing')
    verifyTracing = tracingFunctions.verifyTracing
    endSpan = tracingFunctions.endSpan
    
    const {setupTracing} = require('./tracing/tracer')
    tracer = setupTracing(`${tracingConfig.name} - ${pluginName.split('-').slice(1).join('-')}`);
    verifyTracing = (ctx, name) => tracingFunctions.verifyTracing(tracer, ctx, name)
  }
} catch(err){
  /* eslint-disable */console.log(...oo_oo(`182307278_97_2_97_42_4`,'error loading tracing API'))
}

  if (extConfigErr) {
    logger.error(`${gwName}[${pluginName}] ${extConfigErr.message}`)
    logger.error(`${gwName}[${pluginName}] stopping...\n`)
    throw (new Error('Using exception to stop further asynchronous code execution (ensure synchronous logger flush to logfile and exit program), please ignore this one...'))
  }

  if (!config.scim) config.scim = {}
  if (!config.log) config.log = {}
  if (!config.log.loglevel) config.log.loglevel = {}
  if (!config.auth) config.auth = {}
  if (!config.auth.basic) config.auth.basic = []
  if (!config.auth.bearerToken) config.auth.bearerToken = []
  if (!config.auth.bearerJwt) config.auth.bearerJwt = []
  if (!config.auth.bearerJwtAzure) config.auth.bearerJwtAzure = []
  if (!config.auth.bearerOAuth) config.auth.bearerOAuth = []
  if (!config.auth.passThrough) config.auth.passThrough = {}
  config.auth.oauthTokenStore = {} // oauth token store
  if (!config.certificate) config.certificate = {}
  if (!config.certificate.pfx) config.certificate.pfx = {}
  if (!config.emailOnError) config.emailOnError = {}
  if (!config.emailOnError.smtp) config.emailOnError.smtp = {}
  if (!config.kubernetes) config.kubernetes = {}

  if (config.ipAllowList && Array.isArray(config.ipAllowList) && config.ipAllowList.length > 0) {
    ipAllowListChecker = createChecker(config.ipAllowList)
  }

  const handler = {}
  handler.Users = handler.users = {
    description: 'User',
    getMethod: 'getUsers',
    modifyMethod: 'modifyUser',
    createMethod: 'createUser',
    deleteMethod: 'deleteUser'
  }
  handler.Groups = handler.groups = {
    description: 'Group',
    getMethod: 'getGroups',
    modifyMethod: 'modifyGroup',
    createMethod: 'createGroup',
    deleteMethod: 'deleteGroup'
  }
  handler.servicePlans = handler.serviceplans = { // plugin-azure using "CustomSCIM"
    description: 'ServicePlan',
    getMethod: 'getServicePlans',
    modifyMethod: 'modifyServicePlan',
    createMethod: 'createServicePlan',
    deleteMethod: 'deleteServicePlan'
  }
  handler.healthCheck = handler.healthCheck = { 
    description: 'healthCheck',
    getMethod: 'getHealthCheck',
    
  }

  let foundBasic = false
  let foundBearerToken = false
  let foundBearerJwtAzure = false
  let foundBearerJwt = false
  let foundBearerOAuth = false
  let foundPassThrough = false
  let pwPfxPassword

  if (Array.isArray(config.auth.basic)) {
    const arr = config.auth.basic
    for (let i = 0; i < arr.length; i++) {
      try {
        if (arr[i].password) arr[i].password = ScimGateway.prototype.getPassword(`scimgateway.auth.basic[${i}].password`, configFile)
      } catch (err) {
        logger.error(`${gwName}[${pluginName}] getPassword error: ${err.message}`)
        throw err // above logger.error included because this unhanledExcepton will be handled by winston and may fail with an other internal winston error e.g. related to memoryUsage collection logic when running in unikernel
      }
      if (arr[i].username && arr[i].password) foundBasic = true
    }
    if (!foundBasic) config.auth.basic = []
  }

  if (Array.isArray(config.auth.bearerToken)) {
    const arr = config.auth.bearerToken
    for (let i = 0; i < arr.length; i++) {
      if (arr[i].token) {
        try {
          arr[i].token = ScimGateway.prototype.getPassword(`scimgateway.auth.bearerToken[${i}].token`, configFile)
        } catch (err) {
          logger.error(`${gwName}[${pluginName}] getPassword error: ${err.message}`)
          throw err
        }
        if (arr[i].token) foundBearerToken = true
      }
    }
    if (!foundBearerToken) config.auth.bearerToken = []
  }

  if (Array.isArray(config.auth.bearerJwtAzure)) {
    const issuers = []
    const arr = config.auth.bearerJwtAzure
    for (let i = 0; i < arr.length; i++) {
      if (arr[i].tenantIdGUID) {
        issuers.push(`https://sts.windows.net/${arr[i].tenantIdGUID}/`)
      }
    }
    if (issuers.length > 0) {
      foundBearerJwtAzure = true
      const azureOptions = {
        validateIssuer: true,
        passReqToCallback: false,
        loggingLevel: null,
        // identityMetadata: `https://login.microsoftonline.com/${tenantIdGUID}/.well-known/openid-configuration`,
        identityMetadata: 'https://login.microsoftonline.com/organizations/v2.0/.well-known/openid-configuration',
        clientID: '00000014-0000-0000-c000-000000000000', // Well known appid: Microsoft.Azure.SyncFabric
        audience: [
          // Well known appid: Issued for accessing Windows Azure Active Directory Graph Webservice
          '00000002-0000-0000-c000-000000000000',
          // Appid used for SCIM provisioning for non-gallery applications. See changes introduced, in reverse cronological order:
          // - https://github.com/MicrosoftDocs/azure-docs/commit/f6997c0952d2ad4f33ce7f5339eeb83c21b51f1e
          // - https://github.com/MicrosoftDocs/azure-docs/commit/64525fea0675a73b2e6b8fe42fbd03ee568cadfc
          '8adf8e6e-67b2-4cf2-a259-e3dc5476c621'
        ],
        issuer: issuers // array => passport.authenticate supports more than one AAD tenant
      }

      passport.use(new OIDCBearerStrategy(azureOptions, (token, callback) => { // using named strategy = tenantIdGUID, passport.authenticate then using name
        callback(null, token.sub, token) // Azure SyncFabric don't send user info claims, returning claim token.sub as user
      }))
    } else {
      config.auth.bearerJwtAzure = []
    }
  }

  if (Array.isArray(config.auth.bearerJwt)) {
    const arr = config.auth.bearerJwt
    for (let i = 0; i < arr.length; i++) {
      try {
        if (arr[i].secret) arr[i].secret = ScimGateway.prototype.getPassword(`scimgateway.auth.bearerJwt[${i}].secret`, configFile)
      } catch (err) {
        logger.error(`${gwName}[${pluginName}] getPassword error: ${err.message}`)
        throw err
      }
      if ((arr[i].options && arr[i].options.issuer) && (arr[i].secret || arr[i].publicKey)) {
        foundBearerJwt = true
        if (arr[i].publicKey) { // create publicKeyContent
          try {
            arr[i].publicKeyContent = fs.readFileSync(`${configDir}/certs/${arr[i].publicKey}`)
          } catch (err) {
            arr.splice(i, 1) // delete
            foundBearerJwt = false
            err.message = `failed reading file defined in configuration auth.bearerJwt: ${err.message}`
            logger.error(err.message)
          }
        }
      } else arr.splice(i, 1) // delete
    }
    if (!foundBearerJwt) config.auth.bearerJwt = []
  }

  if (Array.isArray(config.auth.bearerOAuth)) {
    const arr = config.auth.bearerOAuth
    for (let i = 0; i < arr.length; i++) {
      try {
        if (arr[i].client_secret) arr[i].client_secret = ScimGateway.prototype.getPassword(`scimgateway.auth.bearerOAuth[${i}].client_secret`, configFile)
      } catch (err) {
        logger.error(`${gwName}[${pluginName}] getPassword error: ${err.message}`)
        throw err // above logger.error included because this unhanledExcepton will be handled by winston and may fail with an other internal winston error e.g. related to memoryUsage collection logic when running in unikernel
      }
      if (arr[i].client_secret && arr[i].client_id) foundBearerOAuth = true
    }
    if (!foundBearerOAuth) config.auth.bearerOAuth = []
  }

  if (config.auth.passThrough.enabled === true) foundPassThrough = true

  if (config.certificate.pfx.password) pwPfxPassword = ScimGateway.prototype.getPassword('scimgateway.certificate.pfx.password', configFile)
  if (config.emailOnError.smtp.password) config.emailOnError.smtp.password = ScimGateway.prototype.getPassword('scimgateway.emailOnError.smtp.password', configFile)

  if (!foundBasic && !foundBearerToken && !foundBearerJwtAzure && !foundBearerJwt && !foundBearerOAuth && !foundPassThrough) {
    logger.error(`${gwName}[${pluginName}] Scimgateway password decryption failed or no password defined, or no auth methods configured`)
    logger.error(`${gwName}[${pluginName}] stopping...\n`)
    throw (new Error('Using exception to stop further asynchronous code execution (ensure synchronous logger flush to logfile and exit program), please ignore this one...'))
  }

  try {
    if (!fs.existsSync(configDir + '/wsdls')) fs.mkdirSync(configDir + '/wsdls')
    if (!fs.existsSync(configDir + '/certs')) fs.mkdirSync(configDir + '/certs')
    if (!fs.existsSync(configDir + '/schemas')) fs.mkdirSync(configDir + '/schemas')
  } catch (err) {}

  let isScimv2 = false
  if (config.scim.version === '2.0' || config.scim.version === 2) {
    isScimv2 = true
    scimDef = require('../lib/scimdef-v2')
  } else scimDef = require('../lib/scimdef-v1')

  if (config.scim.customSchema) { // merge plugin custom schema extension into core schemas
    let custom
    try {
      custom = JSON.parse(fs.readFileSync(`${configDir}/schemas/${config.scim.customSchema}`, 'utf8'))
    } catch (err) {
      throw new Error(`failed reading file defined in configuration "scim.customSchema": ${err.message}`)
    }
    if (!Array.isArray(custom)) custom = [custom]
    const schemas = ['User', 'Group']
    let customMerged = false
    for (let i = 0; i < schemas.length; i++) {
      const schema = scimDef.Schemas.Resources.find(el => el.name === schemas[i])
      const customSchema = custom.find(el => el.name === schemas[i])
      if (schema && customSchema && Array.isArray(customSchema.attributes)) {
        const arr1 = schema.attributes // core:1.0/2.0 schema
        const arr2 = customSchema.attributes
        schema.attributes = arr2.filter(arr2Obj => { // only merge attributes (objects) having unique name into core schema
          if (!arr1.some(arr1Obj => arr1Obj.name === arr2Obj.name)) {
            customMerged = true
            if (!isScimv2) arr2Obj.schema = 'urn:scim:schemas:core:1.0'
            return arr2Obj
          }
          return undefined
        }).concat(arr1)
      }
    }
    if (!customMerged) {
      const err = [
        'No custom SCIM schema attributes have been merged. Make sure using correct format e.g. ',
        '[{"name": "User", "attributes" : [...]}]. ',
        'Also make sure attribute names in attributes array do not conflict with core:1.0/2.0 SCIM attribute names'
      ].join()
      throw new Error(err)
    }
  }

  this.testmodeusers = scimDef.TestmodeUsers.Resources // exposed and used by plugin-loki
  this.testmodegroups = scimDef.TestmodeGroups.Resources // exposed and used by plugin-loki

  // multiValueTypes array contains attributes that will be used by "type converted objects" logic
  // groups, roles, and members are excluded
  // default: ['emails','phoneNumbers','ims','photos','addresses','entitlements','x509Certificates']
  // configuration skipTypeConvert = true disables logic by empty multiValueTypes array
  if (config.scim.skipTypeConvert === true) multiValueTypes = []
  else {
    multiValueTypes = getMultivalueTypes('User', scimDef) // not icluding 'Group' => 'members' are excluded
    for (let i = 0; i < multiValueTypes.length; i++) {
      if (multiValueTypes[i] === 'groups' || multiValueTypes[i] === 'roles' || multiValueTypes[i] === 'members') {
        multiValueTypes.splice(i, 1) // delete
        i -= 1
      }
    }
  }

  const logResult = async (ctx, next) => {
    const started = Date.now()
    await next() // once all middleware below completes, this continues
    const ellapsed = (Date.now() - started) + 'ms' // ctx.set('X-ResponseTime', ellapsed)
    const res = {
      statusCode: ctx.response.status,
      statusMessage: ctx.response.message,
      body: ctx.response.body
    }
    let userName
    const [authType, authToken] = (ctx.request.header.authorization || '').split(' ') // [0] = 'Basic' or 'Bearer'
    if (authType === 'Basic') [userName] = (Buffer.from(authToken, 'base64').toString() || '').split(':')
    if (!userName && authType === 'Bearer') userName = 'token'
    if (ctx.request.url !== '/favicon.ico') {
      if (ctx.response.status < 200 || ctx.response.status > 299) {
        let isEndpointAccessDenied = false
        if (res.body?.detail) {
          if (res.body.detail.includes('\"statusCode\":401')) isEndpointAccessDenied= true // eslint-disable-line
        } else if (res.body?.Errors) {
          if (Array.isArray(res.body.Errors) && res.body.Errors[0].description && res.body.Errors[0].description.includes('\"statusCode\":401')) { // eslint-disable-line
            isEndpointAccessDenied = true
          }
        }
        if (isEndpointAccessDenied) { // don't reveal original SCIM error message details related to access denied (e.g. using Auth PassThrough)
          ctx.response.set('Content-Type', 'application/json; charset=utf-8')
          ctx.response.status = 401 // ctx.response.message becomes default 'Unauthorized'
          ctx.response.body = { error: 'Access denied' }
          res.statusCode = ctx.response.status
          res.statusMessage = ctx.response.message
          res.body = ctx.response.body
        }
        logger.error(`${gwName}[${pluginName}] ${ellapsed} ${ctx.request.ipcli} ${userName} ${ctx.request.method} ${ctx.request.href} Inbound = ${JSON.stringify(ctx.request.body)} Outbound = ${JSON.stringify(res)}${(config.log.loglevel.file === 'debug' && ctx.request.url !== '/ping') ? '\n' : ''}`)
      } else logger.info(`${gwName}[${pluginName}] ${ellapsed} ${ctx.request.ipcli} ${userName} ${ctx.request.method} ${ctx.request.href} Inbound = ${JSON.stringify(ctx.request.body)} Outbound = ${JSON.stringify(res)}${(config.log.loglevel.file === 'debug' && ctx.request.url !== '/ping') ? '\n' : ''}`)
      requestCounter += 1 // logged on exit (not win process termination)
    }
    if (ctx.response.body && typeof ctx.response.body === 'object' && ctx.response.status !== 401) ctx.set('Content-Type', 'application/scim+json; charset=utf-8')
  }

  // start auth methods - used by auth
  const basic = (baseEntity, method, authType, authToken, url) => {
    return new Promise((resolve, reject) => { // basic auth
      if (url === '/ping' || url.endsWith('/oauth/token') || url === '/_ah/start' || url === '/_ah/stop' || url === '/favicon.ico') resolve(true) // no auth
      if (authType !== 'Basic') resolve(false)
      if (!foundBasic) resolve(false)
      if (foundPassThrough && this.authPassThroughAllowed) resolve(false)
      const [userName, userPassword] = (Buffer.from(authToken, 'base64').toString() || '').split(':')
      if (!userName || !userPassword) {
        return reject(new Error(`authentication failed for user ${userName}`))
      }
      const arr = config.auth.basic
      for (let i = 0; i < arr.length; i++) {
        if (arr[i].username === userName && arr[i].password === userPassword) { // authentication OK
          if (arr[i].baseEntities) {
            if (Array.isArray(arr[i].baseEntities) && arr[i].baseEntities.length > 0) {
              if (!baseEntity) return reject(new Error(`baseEntity=${baseEntity} not allowed for user ${arr[i].username} according to basic configuration baseEntitites=${arr[i].baseEntities}`))
              if (!arr[i].baseEntities.includes(baseEntity)) return reject(new Error(`baseEntity=${baseEntity} not allowed for user ${arr[i].username} according to basic configuration baseEntitites=${arr[i].baseEntities}`))
            }
          }
          if (arr[i].readOnly === true && method !== 'GET') return reject(new Error(`only allowing readOnly for user ${arr[i].username} according to basic configuration readOnly=true`))
          return resolve(true)
        }
      }
      reject(new Error(`authentication failed for user ${userName}`))
    })
  }

  const bearerToken = (baseEntity, method, authType, authToken) => {
    return new Promise((resolve, reject) => { // bearer token
      if (authType !== 'Bearer' || !authToken) resolve(false)
      if (!foundBearerToken) resolve(false)
      const arr = config.auth.bearerToken
      for (let i = 0; i < arr.length; i++) {
        if (arr[i].token === authToken) { // authentication OK
          if (arr[i].baseEntities) {
            if (Array.isArray(arr[i].baseEntities) && arr[i].baseEntities.length > 0) {
              if (!baseEntity) return reject(new Error(`baseEntity=${baseEntity} not allowed for this bearerToken according to bearerToken configuration baseEntitites=${arr[i].baseEntities}`))
              if (!arr[i].baseEntities.includes(baseEntity)) return reject(new Error(`baseEntity=${baseEntity} not allowed for this bearerToken according to bearerToken configuration baseEntitites=${arr[i].baseEntities}`))
            }
          }
          if (arr[i].readOnly === true && method !== 'GET') return reject(new Error('only allowing readOnly for this bearerToken according to bearerToken configuration readOnly=true'))
          return resolve(true)
        }
      }
      reject(new Error('bearerToken authentication failed'))
    })
  }

  const bearerJwtAzure = (baseEntity, ctx, next, authType, authToken) => {
    return new Promise((resolve, reject) => {
      if (authType !== 'Bearer' || !foundBearerJwtAzure) resolve(false) // no azure bearer token
      const payload = jwt.decode(authToken)
      if (!payload) resolve(false)
      if (!payload.iss) resolve(false)
      if (payload.iss.indexOf('https://sts.windows.net') !== 0) resolve(false)
      passport.authenticate('oauth-bearer', { session: false }, (err, user, info) => {
        if (err) { return reject(err) }
        if (user) { // authenticated OK
          const arr = config.auth.bearerJwtAzure
          for (let i = 0; i < arr.length; i++) {
            if (arr[i].tenantIdGUID && payload.iss.includes(arr[i].tenantIdGUID)) {
              if (arr[i].baseEntities) {
                if (Array.isArray(arr[i].baseEntities) && arr[i].baseEntities.length > 0) {
                  if (!baseEntity) return reject(new Error(`baseEntity=${baseEntity} not allowed for user ${arr[i].tenantIdGUID} according to bearerJwtAzure configuration baseEntitites=${arr[i].baseEntities}`))
                  if (!arr[i].baseEntities.includes(baseEntity)) return reject(new Error(`baseEntity=${baseEntity} not allowed for user ${arr[i].tenantIdGUID} according to bearerJwtAzure configuration baseEntitites=${arr[i].baseEntities}`))
                }
              }
              if (arr[i].readOnly === true && ctx.request.method !== 'GET') return reject(new Error(`only allowing readOnly for user ${arr[i].tenantIdGUID} according to bearerJwtAzure configuration readOnly=true`))
            }
          }
          resolve(true)
        } else reject(new Error(`Azure JWT authorization failed: ${info}`))
      })(ctx, next)
    })
  }

  const jwtVerify = (baseEntity, method, el, authToken) => { // used by bearerJwt
    return new Promise((resolve, reject) => {
      jwt.verify(authToken, (el.secret) ? el.secret : el.publicKeyContent, el.options, (err, decoded) => {
        if (err) resolve(false)
        else {
          if (el.baseEntities) {
            if (Array.isArray(el.baseEntities) && el.baseEntities.length > 0) {
              if (!baseEntity) return resolve(false)
              if (!el.baseEntities.includes(baseEntity)) return resolve(false)
            }
          }
          if (el.readOnly === true && method !== 'GET') return resolve(false)
          resolve(true) // authorization OK
        }
      })
    })
  }

  const bearerJwt = async (baseEntity, method, authType, authToken) => {
    if (authType !== 'Bearer' || !foundBearerJwt) return false // no standard jwt bearer token
    const payload = jwt.decode(authToken)
    if (!payload) return false
    if (payload.iss && payload.iss.indexOf('https://sts.windows.net') === 0) return false // azure - handled by bearerJwtAzure
    const promises = []
    const arr = config.auth.bearerJwt
    for (let i = 0; i < arr.length; i++) {
      promises.push(jwtVerify(baseEntity, method, arr[i], authToken))
    }
    const arrResolve = await Promise.all(promises).catch((err) => { throw (err) })
    for (const i in arrResolve) {
      if (arrResolve[i]) return true
    }
    throw new Error('JWT authentication failed')
  }

  const bearerOAuth = (baseEntity, method, authType, authToken) => {
    return new Promise((resolve, reject) => { // bearer token
      if (authType !== 'Bearer' || !authToken) resolve(false)
      if (!foundBearerOAuth || !authToken) resolve(false)
      // config.auth.oauthTokenStore is autmatically generated by token create having syntax:
      // { config.auth.oauthTokenStore: <token>: { expireDate: <timestamp>, readOnly: <copy-from-config>, baseEntities: [ <copy-from-config> ], isTokenRequested: true }}
      const arr = config.auth.bearerOAuth
      if (config.auth.oauthTokenStore[authToken]) { // authentication OK
        const tokenObj = config.auth.oauthTokenStore[authToken]
        if (Date.now() > tokenObj.expireDate) {
          delete config.auth.oauthTokenStore[authToken]
          const err = new Error('OAuth access token expired')
          err.token_error = 'invalid_token'
          err.token_error_description = 'The access token expired'
          return reject(err)
        }
        if (tokenObj.baseEntities) {
          if (Array.isArray(tokenObj.baseEntities) && tokenObj.baseEntities.length > 0) {
            if (!baseEntity) return reject(new Error(`baseEntity=${baseEntity} not allowed for this bearerOAuth according to bearerOAuth configuration baseEntitites=${tokenObj.baseEntities}`))
            if (!tokenObj.baseEntities.includes(baseEntity)) return reject(new Error(`baseEntity=${baseEntity} not allowed for this bearerOAuth according to bearerOAuth configuration baseEntitites=${tokenObj.baseEntities}`))
          }
        }
        if (tokenObj.readOnly === true && method !== 'GET') return reject(new Error('only allowing readOnly for this bearerOAuth according to bearerOAuth configuration readOnly=true'))
        return resolve(true)
      } else {
        for (let i = 0; i < arr.length; i++) { // resolve if token memory store have been cleared because of a gateway restart
          if (utils.getEncrypted(authToken, arr[i].client_secret) === arr[i].client_secret && !arr[i].isTokenRequested) {
            arr[i].isTokenRequested = true // flagged as true to not allow repeated resolvements because token will also be cleared when expired
            const baseEntities = utils.copyObj(arr[i].baseEntities)
            let expires
            let readOnly = false
            if (arr[i].readOnly && arr[i].readOnly === true) readOnly = true
            if (arr[i].expires_in && !isNaN(arr[i].expires_in)) expires = arr[i].expires_in
            else expires = oAuthTokenExpire
            config.auth.oauthTokenStore[authToken] = {
              expireDate: Date.now() + expires * 1000,
              readOnly: readOnly,
              baseEntities: baseEntities
            }
            return resolve(true)
          }
        }
      }
      reject(new Error('OAuth authentication failed'))
    })
  }

  const authPassThrough = async (baseEntity, method, authType, authToken, ctx) => {
    if (!foundPassThrough || !this.authPassThroughAllowed) return false
    if (!authToken) return false
    if (authType === 'Basic') {
      const [userName, userPassword] = (Buffer.from(authToken, 'base64').toString() || '').split(':')
      if (!userName || !userPassword) return false
    }
    const obj = config.auth.passThrough
    if (obj.baseEntities) {
      if (Array.isArray(obj.baseEntities) && obj.baseEntities.length > 0) {
        if (!baseEntity || !obj.baseEntities.includes(baseEntity)) throw new Error(`baseEntity=${baseEntity} not allowed for passThrough according to passThrough configuration baseEntitites=${obj.baseEntities}`)
      }
    }
    if (obj.readOnly === true && method !== 'GET') throw new Error('only allowing readOnly for passThrough according to passThrough configuration readOnly=true')
    ctx.ctxCopy = {}
    ctx.ctxCopy.request = {}
    ctx.ctxCopy.request.header = Object.assign({}, ctx.request.header)
    return true
  }

  // end auth methods - used by auth

  const auth = async (ctx, next) => { // authentication/authorization
    const [authType, authToken] = (ctx.request.header.authorization || '').split(' ') // [0] = 'Basic' or 'Bearer'
    let baseEntity
    const arr = ctx.request.url.split('/')
    if (arr.length > 0) {
      const entity = arr[1].split('?')[0]
      if (!['Users', 'Groups', 'Schemas', 'ServiceProviderConfigs', 'scim'].includes(entity)) baseEntity = entity
    }
    try { // authenticate
      const arrResolve = await Promise.all([
        basic(baseEntity, ctx.request.method, authType, authToken, ctx.url),
        bearerToken(baseEntity, ctx.request.method, authType, authToken),
        bearerJwtAzure(baseEntity, ctx, next, authType, authToken),
        bearerJwt(baseEntity, ctx.request.method, authType, authToken),
        bearerOAuth(baseEntity, ctx.request.method, authType, authToken),
        authPassThrough(baseEntity, ctx.request.method, authType, authToken, ctx)])
        .catch((err) => { throw (err) })
      for (const i in arrResolve) {
        if (arrResolve[i]) return next() // auth OK - continue with routes
      }
      // all false - invalid auth method or missing pluging config
      let err
      if (authType.length < 1) err = new Error(`${ctx.url} request is missing authentication information`)
      else {
        err = new Error(`${ctx.url} request having unsupported authentication or plugin configuration is missing`)
        logger.debug(`${gwName}[${pluginName}] request authToken = ${authToken}`)
        logger.debug(`${gwName}[${pluginName}] request jwt.decode(authToken) = ${JSON.stringify(jwt.decode(authToken))}`)
      }
      if (authType === 'Bearer') ctx.set('WWW-Authenticate', 'Bearer realm=""')
      else if (foundBasic) ctx.set('WWW-Authenticate', 'Basic realm=""')
      ctx.set('Content-Type', 'application/json; charset=utf-8')
      ctx.status = 401
      ctx.body = { error: 'Access denied' }
      if (ctx.url !== '/favicon.ico') logger.error(`${gwName}[${pluginName}] ${err.message}`)
    } catch (err) {
      const body = {}
      if (authType === 'Bearer') {
        let str = 'realm=""'
        if (err.token_error) {
          str += `, error="${err.token_error}"`
          body.error = err.token_error
        }
        if (err.token_error_description) {
          str += `, error_description="${err.token_error_description}"`
          body.error_description = err.token_error_description
        }
        ctx.set('WWW-Authenticate', `Bearer ${str}`)
      } else ctx.set('WWW-Authenticate', 'Basic realm=""')
      ctx.set('Content-Type', 'application/json; charset=utf-8')
      ctx.status = 401
      if (Object.keys(body).length > 0) ctx.body = body
      else ctx.body = { error: 'Access denied' }
      if (pwErrCount < 3) {
        pwErrCount += 1
        logger.error(`${gwName}[${pluginName}] ${ctx.url} ${err.message}`)
      } else { // delay brute force attempts
        logger.error(`${gwName}[${pluginName}] ${ctx.url} ${err.message} => delaying response with 2 minutes to prevent brute force`)
        return new Promise((resolve) => {
          setTimeout(() => {
            resolve(ctx)
          }, 1000 * 60 * 2)
        })
      }
    }
  } // authentication

  const verifyContentType = (ctx, next) => {
    return new Promise((resolve) => {
      if (ctx.request.length) { // body is included - invalid content-type gives empty body (koa-bodyparser)
        const contentType = ctx.request.type.toLowerCase()
        if (contentType === 'application/json' || contentType === 'application/scim+json') return resolve(next())
        if (ctx.url.endsWith('/oauth/token')) return resolve(next())
        ctx.status = 415
        ctx.body = 'Content-Type header must be \'application/json\' or \'application/scim+json\''
        return resolve(ctx)
      }
      resolve(next())
    })
  }

  const ipAllowList = (ctx, next) => {
    return new Promise((resolve) => {
      ctx.request.ipcli = ctx.req.headers['x-forwarded-for'] || ctx.req.connection.remoteAddress
      ctx.request.ipcli = ctx.request.ipcli.split(',')[0] // used by logResult
      if (!ipAllowListChecker) return resolve(next())
      if (ipAllowListChecker(ctx.request.ipcli)) return resolve(next())
      logger.debug(`${gwName}[${pluginName}] client ip ${ctx.request.ipcli} not in ipAllowList`)
      ctx.status = 401
      ctx.body = 'Access denied'
      resolve(ctx)
    })
  }

  
  

  const app = new Koa()
  const router = new Router()

  useListeners(ScimGateway.prototype.endpointMapper, config.auth, require(configFile).endpoint.map)

app.use(cors({ origin: '*', credentials: true }));

  // Middleware run in the order they are defined and communicates through ctx
  // There is no return value, if there were it would be ignored
  app.use(logResult)
  app.use(bodyParser({ // parsed body store in ctx.request.body
    enableTypes: ['json', 'form'],
    extendTypes: { json: ['application/scim+json', 'text/plain'] },
    formTypes: { form: ['application/x-www-form-urlencoded'] },
    jsonLimit: (!config.payloadSize) ? undefined : config.payloadSize // default '1mb'
  }))

  // Start tracing (if enabled)
  app.use(async (ctx, next) => {
    return new Promise(async(resolve) => {
      span = verifyTracing(ctx, `${ctx.request.method} - ${ctx.request.path}`)
      resolve(next());
      })
  })

  // Middleware
  app.use(async (ctx, next) => {
    return new Promise(async(resolve) => {
    const { method } = ctx.request
      if(!['POST', 'PUT', 'PATCH'].includes(method)) {
        resolve(next());
        return;
      }

      async function runInterceptors(){
        let res = await fetchInterceptors(ctx, caches, verifyTracing)
        if(res){
          resolve(next());
        } else{
          resolve(ctx)
          endSpan(ctx, span, requestSpan)
        }
      }

      if(api && tracingConfig.enabled){
        TelemetryWrapper(api, async () => {
          runInterceptors()
        })
      } else{
        runInterceptors()
      }
      
    })
  })


  app.use(async (ctx, next) => {
    return new Promise(async(resolve) => {
    
      async function runAdapters(){        
        const notificationRes = await fetchNotification(ctx, 'before', caches, verifyTracing)
        if(notificationRes){
          resolve(next());  
        } else{
          resolve(ctx)
          endSpan(ctx, span, requestSpan)
        }
      }

      if(api && tracingConfig.enabled){
        TelemetryWrapper(api, async () => {
          runAdapters()
        })
      } else{
        runAdapters()
      }
    })
  })
  
  


  app.use(ipAllowList)
  app.use(auth) // authentication before routes
  app.use(verifyContentType)
  app.use(router.routes())
  app.use(router.allowedMethods())


  app.on('error', (err, ctx) => { // catching none try/catch in app middleware, also bodyparser and body not json
    logger.error(`${gwName}[${pluginName}] Koa method: ${ctx.method} url: ${ctx.origin + ctx.path} body: ${JSON.stringify(ctx.request.body)} error: ${err.message}`)
  })

  router.get('/ping', async (ctx) => { // auth not required
    const tx = 'hello'

    ctx.set('Content-Type', 'text/plain; charset=utf-8')
    ctx.body = tx
  })

  // Google App Engine B-class instance start/stop request
  router.get(['/_ah/start', '/_ah/stop'], async (ctx) => {
    const cli = ctx.request.ipcli
    const ver = process.env.GAE_VERSION
    if (!cli || cli !== '0.1.0.3' || !ver || !ctx.origin.includes(`.${ver}.`)) { // ctx.origin = http://<instance>.<version>.<project-id>.<region>.r.appspot.com
      ctx.status = 403 // request not coming from GCP App Engine
      return
    }
    // could have some start/stop logic here
    ctx.status = 200
  })

  // Initial connection, step #1: GET /ServiceProviderConfigs
  // If not included => Provisioning will always use GET /Users without any paramenters
  // scimv1 = ServiceProviderConfigs, scimv2 ServiceProviderConfig
  router.get(['/(|scim/)(ServiceProviderConfigs|ServiceProviderConfig)',
    '/:baseEntity/(|scim/)(ServiceProviderConfigs|ServiceProviderConfig)'], async (ctx) => {
    const tx = scimDef.ServiceProviderConfigs
    const location = ctx.origin + ctx.path
    if (tx.meta) tx.meta.location = location
    else {
      tx.meta = {"resourceType": "ServiceProviderConfig"}
      tx.meta.location = location
    }
    ctx.body = tx
    logger.debug(`${gwName}[${pluginName}] GET ${ctx.originalUrl} Response = ${JSON.stringify(tx)}`)
  })

  // Initial connection, step #2: GET /Schemas
  router.get(['/(|scim/)Schemas', '/:baseEntity/(|scim/)Schemas'], async (ctx) => {
    let tx = scimDef.Schemas
    tx = addResources(tx)
    tx = addSchemas(tx, null, isScimv2)
    ctx.body = tx
  })

  // oauth token request
  router.post(['/(|scim/)oauth/token', '/:baseEntity/(|scim/)oauth/token'], async (ctx) => {
    logger.debug(`${gwName}[${pluginName}] [oauth] token request`)
    if (!foundBearerOAuth) {
      logger.error(`${gwName}[${pluginName}] [oauth] token request, but plugin is missing config.auth.bearerOAuth configuration`)
      ctx.status = 500
      return
    }

    const jsonBody = ctx.request.body
    const [authType, authToken] = (ctx.request.header.authorization || '').split(' ') // [0] = 'Basic'
    if (authType === 'Basic') { // id and secret may be in authorization header if not already included in body
      const [id, secret] = (Buffer.from(authToken, 'base64').toString() || '').split(':')
      if (jsonBody.grant_type && id && secret) {
        if (jsonBody.grant_type === 'client_credentials' || jsonBody.grant_type === 'refresh_token') { // don't use refresh_token but allowing as type
          jsonBody.client_id = id
          jsonBody.client_secret = secret
        }
      }
    }

    let expires
    let token
    let readOnly = false
    let baseEntities
    let err
    let errDescr
    if (!jsonBody.grant_type || (jsonBody.grant_type !== 'client_credentials' && jsonBody.grant_type !== 'refresh_token')) {
      err = 'invalid_request'
      errDescr = 'request type must be Client Credentials (grant_type=client_credentials)'
    }

    if (!err) {
      const arr = config.auth.bearerOAuth
      for (let i = 0; i < arr.length; i++) {
        if (!arr[i].client_id || !arr[i].client_secret) continue
        if (arr[i].client_id === jsonBody.client_id && arr[i].client_secret === jsonBody.client_secret) { // authentication OK
          token = utils.getEncrypted(jsonBody.client_secret, jsonBody.client_secret)
          baseEntities = utils.copyObj(arr[i].baseEntities)
          if (arr[i].readOnly && arr[i].readOnly === true) readOnly = true
          if (arr[i].expires_in && !isNaN(arr[i].expires_in)) expires = arr[i].expires_in
          else expires = oAuthTokenExpire
          arr[i].isTokenRequested = true
          break
        }
      }
      if (!token) {
        err = 'invalid_client'
        errDescr = 'incorrect or missing client_id/client_secret'
        if (pwErrCount < 3) {
          pwErrCount += 1
        } else { // delay brute force attempts
          logger.error(`${gwName}[${pluginName}] [oauth] ${ctx.url} ${errDescr} => delaying response with 2 minutes to prevent brute force`)
          return new Promise((resolve) => {
            setTimeout(() => {
              resolve(ctx)
            }, 1000 * 60 * 2)
          })
        }
      }
    }

    if (err) {
      logger.error(`${gwName}[${pluginName}] [oauth] token request client_id: ${jsonBody ? jsonBody.client_id : ''} error: ${errDescr}`)
      ctx.status = 400
      ctx.body = {
        error: err,
        error_description: errDescr
      }
      return
    }

    const dtNow = Date.now()
    for (const i in config.auth.oauthTokenStore) { // cleanup any expired tokens
      const tokenObj = config.auth.oauthTokenStore[i]
      if (dtNow > tokenObj.expireDate) {
        delete config.auth.oauthTokenStore[i]
      }
    }

    config.auth.oauthTokenStore[token] = { // update token store
      expireDate: dtNow + expires * 1000, // 1 hour
      readOnly: readOnly,
      baseEntities: baseEntities
    }

    const tx = {
      access_token: token,
      token_type: 'Bearer',
      expires_in: expires,
      refresh_token: token // ignored by scimgateway, but maybe used by client
    }

    ctx.set('Cache-Control', 'no-store')
    ctx.body = tx
  })

  router.get(['/(|scim/)Schemas/:id', '/:baseEntity/(|scim/)Schemas/:id'], async (ctx) => { // e.g /Schemas/Users | Groups | ServiceProviderConfigs
    let schemaName = ctx.params.id
    if (schemaName.substr(schemaName.length - 1) === 's') schemaName = schemaName.substr(0, schemaName.length - 1)
    const tx = scimDef.Schemas.Resources.find(el => el.name === schemaName)
    if (!tx) {
      ctx.status = 404
      let err = new Error(`Schema '${schemaName}' not found`)
      err = jsonErr(config.scim.version, pluginName, ctx.status, err)
      ctx.body = err
    } else {
      ctx.body = tx
    }
  })

  router.get(['/(|scim/)(ResourceTypes|ResourceType)',
    '/:baseEntity/(|scim/)(ResourceTypes|ResourceType)'], async (ctx) => { // ResourceTypes according to v2 specification
    const tx = scimDef.ResourceType
    ctx.body = tx
  })

  // ==========================================
  //           getUser (unique)
  //           getGroup (unique)
  // ==========================================
  router.get([`/(|scim/)(!${undefined}|Users|Groups|servicePlans)/:id`,
  `/:baseEntity/(|scim/)(!${undefined}|Users|Groups|servicePlans)/:id`], async (ctx) => {

    return await TelemetryWrapper(api, async () => {
      requestSpan = verifyTracing(ctx,  'Request')

    if (ctx.query.attributes) ctx.query.attributes = ctx.query.attributes.split(',').map(item => item.trim()).join()
    if (ctx.query.excludedAttributes) ctx.query.excludedAttributes = ctx.query.excludedAttributes.split(',').map(item => item.trim()).join()
    let u = ctx.originalUrl.substr(0, ctx.originalUrl.lastIndexOf('/'))
    u = u.substr(u.lastIndexOf('/') + 1) // u = Users, Groups
    const handle = handler[u]
    const id = decodeURIComponent(require('path').basename(ctx.params.id, '.json')) // supports <id>.json

    const getObj = {
      attribute: 'id',
      operator: 'eq',
      value: id
    }

    logger.debug(`${gwName}[${pluginName}] [Get ${handle.description}s] ${getObj.attribute}=${getObj.value}`)
    logger.debug(`${gwName}[${pluginName}] calling "${handle.getMethod}" and awaiting result`)

    try {
      const res = await this[handle.getMethod](ctx.params.baseEntity, utils.copyObj(getObj), ctx.query.attributes ? ctx.query.attributes.split(',').map(item => item.trim()) : [], ctx.ctxCopy)

      let scimdata = {
        Resources: [],
        totalResults: null
      }
      if (res) {
        if (res.Resources && Array.isArray(res.Resources)) {
          scimdata.Resources = res.Resources
          scimdata.totalResults = res.totalResults
        } else if (Array.isArray(res)) scimdata.Resources = res
        else if (typeof (res) === 'object' && Object.keys(res).length > 0) scimdata.Resources[0] = res
      }

      if (scimdata.Resources.length !== 1) {
        ctx.status = 404
        let err = new Error(`${handle.description} ${getObj.value} not found`)
        err = jsonErr(config.scim.version, pluginName, ctx.status, err)
        ctx.body = err
        endSpan(ctx, span, requestSpan)
        return
      }

      // check for user attribute groups and include if needed
      let userObj = scimdata.Resources[0]
      if (handle.getMethod === handler.users.getMethod && Object.keys(userObj).length > 0 && !userObj.groups && !config.scim.groupMemberOfUser) { // groupMemberOfUser can be set to true for skipping
        let arrAttr = []
        if (ctx.query.attributes) arrAttr = ctx.query.attributes.split(',')
        if ((!ctx.query.attributes || arrAttr.includes('groups')) && typeof this[handler.groups.getMethod] === 'function') { // include groups
          logger.debug(`${gwName}[${pluginName}] calling "${handler.groups.getMethod}" and awaiting result - groups to be included`)
          let res
          try {
            res = await this[handler.groups.getMethod](ctx.params.baseEntity, { attribute: 'members.value', operator: 'eq', value: getObj.value }, ['id', 'displayName'], ctx.ctxCopy)
          } catch (err) {} // method may be implemented but throwing error like groups not supported/implemented
          if (res && res.Resources && Array.isArray(res.Resources) && res.Resources.length > 0) {
            userObj.groups = []
            for (let i = 0; i < res.Resources.length; i++) {
              if (!res.Resources[i].id) continue
              const el = {}
              el.value = res.Resources[i].id
              if (res.Resources[i].displayName) el.display = res.Resources[i].displayName
              if (isScimv2) el.type = 'direct'
              else el.type = { value: 'direct' }
              userObj.groups.push(el) // { "value": "Admins", "display": "Admins", "type": "direct"}
            }
          }
        }
      }
      const location = ctx.origin + ctx.path
      userObj = addPrimaryAttrs(userObj)
      scimdata = utils.stripObj(userObj, ctx.query.attributes, ctx.query.excludedAttributes)
      scimdata = addSchemas(scimdata, handle.description, isScimv2)
      if (scimdata.meta) scimdata.meta.location = location
      else {
        scimdata.meta = {}
        scimdata.meta.location = location
      }
      ctx.body = scimdata
      await fetchNotification(ctx, 'onSuccess', caches, verifyTracing)
    } catch (err) {
      let scimType = errorStatus(err, isScimv2, ctx)
      const e = jsonErr(config.scim.version, pluginName, ctx.status, err)
      ctx.body = e
      await fetchNotification(ctx, 'onError', caches, verifyTracing)
    }
    
    endSpan(ctx, span, requestSpan)
    })
  })

  // ==========================================
  //           getUsers
  //           getGroups
  // ==========================================
  router.get(['/(|scim/)(Users|Groups|servicePlans)',
    '/:baseEntity/(|scim/)(Users|Groups|servicePlans)'], async (ctx) => {
      return await TelemetryWrapper(api, async () => {
        requestSpan = verifyTracing(ctx,  'Request')
      
    if (ctx.query.attributes) ctx.query.attributes = ctx.query.attributes.split(',').map(item => item.trim()).join()
    if (ctx.query.excludedAttributes) ctx.query.excludedAttributes = ctx.query.excludedAttributes.split(',').map(item => item.trim()).join()
    if(ctx.originalUrl.at(-1) === '/'){
      ctx.originalUrl = ctx.originalUrl.slice(0, ctx.originalUrl.length-1)
    }
    let u = ctx.originalUrl.substr(ctx.originalUrl.lastIndexOf('/') + 1) // u = Users, Groups, servicePlans, ...
    
    const ui = u.indexOf('?')
    if (ui > 0) u = u.substr(0, ui)
    const handle = handler[u]

    const getObj = {
      attribute: undefined,
      operator: undefined,
      value: undefined,
      rawFilter: ctx.query.filter, // included for advanced filtering
      startIndex: undefined,
      count: undefined
    }

    if (ctx.query.filter) {
      ctx.query.filter = ctx.query.filter.trim()
      const arrFilter = ctx.query.filter.split(' ')
      if (arrFilter.length === 3 || (arrFilter.length > 2 && arrFilter[2].startsWith('"') && arrFilter[arrFilter.length - 1].endsWith('"'))) {
        getObj.attribute = arrFilter[0] // userName
        getObj.operator = arrFilter[1].toLowerCase() // eq
        getObj.value = decodeURIComponent(arrFilter.slice(2).join(' ').replace(/"/g, '')) // bjensen
      }
    }

    let err
    if (getObj.attribute) {
      if (multiValueTypes.includes(getObj.attribute) || getObj.attribute === 'roles') {
        getObj.attribute = `${getObj.attribute}.value` // emails => emails.value
      } else if (getObj.attribute.includes('[')) { // e.g. rawFilter = emails[type eq "work"]
        const rePattern = /^(.*)\[(.*) (.*) (.*)\]$/
        const arrMatches = ctx.query.filter.match(rePattern)
        if (Array.isArray(arrMatches) && arrMatches.length === 5) {
          getObj.attribute = `${arrMatches[1]}.${arrMatches[2]}` // emails.type
          getObj.operator = arrMatches[3]
          getObj.value = arrMatches[4].replace(/"/g, '')
        } else {
          getObj.attribute = undefined
          getObj.operator = undefined
          getObj.value = undefined
        }
      }
      if (getObj.attribute === 'password') {
        err = new Error(`Not accepting password filtering: ${getObj.rawFilter}`)
        err.name = 'invalidFilter'
      }
    } else if (getObj.rawFilter && ![' and ', ' or ', ' not '].some(el => getObj.rawFilter.includes(el))) { // advanced filtering
      // err = new Error(`Invalid filter: ${getObj.rawFilter}`)
      // err.name = 'invalidFilter'
    }
    if (err) {
      let scimType = errorStatus(err, isScimv2, ctx)
      const e = jsonErr(config.scim.version, pluginName, ctx.status, err, scimType)
      ctx.body = e
      return
    }

    //
    // Get user request for retreving common unique attributes:
    // GET = /Users?filter=userName eq "jsmith"&attributes=id,userName
    // GET = /Users?filter=id eq "jsmith"&attributes=id,userName
    //
    // Get user request for retreving all attributes:
    // GET = /Users?filter=userName eq "jsmith"&attributes=ims,locale,name.givenName,externalId,preferredLanguage,userType,id,title,timezone,name.middleName,name.familyName,nickName,name.formatted,meta.location,userName,name.honorificSuffix,meta.version,meta.lastModified,meta.created,name.honorificPrefix,emails,phoneNumbers,photos,x509Certificates.value,profileUrl,roles,active,addresses,displayName,entitlements
    //
    //  ---- retreive all users for a spesific group ----
    //
    // "user member of group" => default - Group having multivalue attribute members containing users userName/id
    // GET = /Groups?filter=members.value eq "bjensen"&attributes=id,displayName,members.value
    //
    // "group member of user" => User having multivalue attribute groups containing value=GroupName
    // GET = /Users?filter=groups.value eq "UserGroup-1"&attributes=groups.value,userName
    //
    //   ---- Azure AD to SCIM Users ----
    //
    // Default SCIM attribute mapping have:
    //   externalId mapped to mailNickname (matching precedence #1)
    //   userName mapped to userPrincipalName
    //
    // Precedence decides filter attribute sent to ScimGateway
    // GET = /scim/Users?filter=externalId eq "jarle_elshaug"
    //
    // ScimGateway accepts externalId (as matching precedence) instead of userName, but userName and externalId must
    // then be mapped to the same AD attribte e.g:
    //
    //   externalId mapped to mailNickname (matching precedence #1)
    //   userName mapped to mailNickname
    // or:
    //   externalId mapped to userPrincipalName (matching precedence #1)
    //   userName mapped to userPrincipalName
    //
    // ---- GROUP ----
    //
    // Get group:
    // GET /Groups?filter=displayName eq "Employees"&attributes=externalId,id,members.value,displayName
    //
    // Azure AD:
    // GET /scim/Groups?excludedAttributes=members&filter=externalId eq "MyGroup"
    //
    // Get group members:
    // GET = /Groups?filter=members.value eq "<user-id>"&attributes=members.value,displayName&startIndex=1&count=100
    //
    //   ---- Azure AD to SCIM Groups ----
    //
    // Default SCIM attribute for GROUP mapping have:
    //   externalId mapped to displayName (matching precedence #1)
    //   displayName mapped to mailNickname
    //
    // ScimGateway accepts externalId (as matching precedence) instead of displayName, but displayName and externalId must
    // then be mapped to the same AD attribute e.g:
    //
    //   externalId mapped to displayName (matching precedence #1)
    //   displayName mapped to displayName
    //
    // ---- servicePlans ----
    // GET /servicePlans?filter=servicePlanName+eq+%22EXCHANGE_S_FOUNDATION%22&attributes=servicePlanName
    //
    // ---- no filtering - simpel filtering - advanced filtering ----
    // GET /Users
    // GET /Groups
    // GET /Users?attributes=userName&startIndex=1&count=100
    // GET /Groups?attributes=displayName
    // GET /Users?filter=meta.created ge "2010-01-01T00:00:00Z"&attributes=userName,id,name.familyName,meta.created
    // GET /Users?filter=emails.value co "@example.com"&attributes=userName,name.familyName,emails&sortBy=name.familyName&sortOrder=descending

    let info = ''
    if (getObj.operator === 'eq' && ['id', 'userName', 'externalId', 'displayName', 'members.value'].includes(getObj.attribute)) info = ` ${getObj.attribute}=${getObj.value}`

    logger.debug(`${gwName}[${pluginName}] [Get ${handle.description}s]${info}`)
    logger.debug(`${gwName}[${pluginName}] calling "${handle.getMethod}" and awaiting result`)
    try {
      getObj.startIndex = ctx.query.startIndex ? parseInt(ctx.query.startIndex) : undefined
      getObj.count = ctx.query.count ? parseInt(ctx.query.count) : undefined
      if (getObj.startIndex && !getObj.count) getObj.count = 200 // defaults to 200 (plugin may override)
      if (getObj.count && !getObj.startIndex) getObj.startIndex = 1

      const res = await this[handle.getMethod](ctx.params.baseEntity, utils.copyObj(getObj), ctx.query.attributes ? ctx.query.attributes.split(',').map(item => item.trim()) : [], ctx.ctxCopy)
      let scimdata = {
        Resources: [],
        totalResults: null
      }
      if (res) {
        if (res.Resources && Array.isArray(res.Resources)) {
          scimdata.Resources = res.Resources
          scimdata.totalResults = res.totalResults
        } else if (Array.isArray(res)) scimdata.Resources = res
        else if (typeof (res) === 'object' && Object.keys(res).length > 0) scimdata.Resources[0] = res
      }

      // check for user attribute groups and include if needed
      if (handle.getMethod === handler.users.getMethod && !config.scim.groupMemberOfUser) { // groupMemberOfUser can be set to true for skipping
        let arrAttr = []
        if (ctx.query.attributes) arrAttr = ctx.query.attributes.split(',')
        if ((!ctx.query.attributes || arrAttr.includes('groups')) && typeof this[handler.groups.getMethod] === 'function') { // include groups
          for (let j = 0; j < scimdata.Resources.length; j++) {
            const userObj = scimdata.Resources[j]
            if (!userObj.id) break
            if (userObj.groups) break
            logger.debug(`${gwName}[${pluginName}] calling "${handler.groups.getMethod}" and awaiting result - groups to be included`)
            let res
            try {
              res = await this[handler.groups.getMethod](ctx.params.baseEntity, { attribute: 'members.value', operator: 'eq', value: decodeURIComponent(userObj.id) }, ['id', 'displayName'], ctx.ctxCopy) // await scimgateway.getUserGroups(baseEntity, userObj.id, 'members.value,displayName')
            } catch (err) {} // method may be implemented but throwing error like groups not supported/implemented
            if (res && res.Resources && Array.isArray(res.Resources) && res.Resources.length > 0) {
              userObj.groups = []
              for (let i = 0; i < res.Resources.length; i++) {
                if (!res.Resources[i].id) continue
                const el = {}
                el.value = res.Resources[i].id
                if (res.Resources[i].displayName) el.display = res.Resources[i].displayName
                if (isScimv2) el.type = 'direct'
                else el.type = { value: 'direct' }
                userObj.groups.push(el) // { "value": "Admins", "display": "Admins", "type": "direct"}
              }
            }
          }
        }
      }

      let location = ctx.origin + ctx.path
      if (ctx.query.attributes || (ctx.query.excludedAttributes && ctx.query.excludedAttributes.includes('meta'))) location = null
      for (let i = 0; i < scimdata.Resources.length; i++) {
        scimdata.Resources[i] = addPrimaryAttrs(scimdata.Resources[i])
        scimdata.Resources[i] = utils.stripObj(scimdata.Resources[i], ctx.query.attributes, ctx.query.excludedAttributes)
      }
      scimdata = addResources(scimdata, ctx.query.startIndex, ctx.query.sortBy, ctx.query.sortOrder)
      scimdata = addSchemas(scimdata, handle.description, isScimv2, location)

      ctx.body = scimdata
      await fetchNotification(ctx, 'onSuccess', caches, verifyTracing)
    } catch (err) {
      let scimType = errorStatus(err, isScimv2, ctx)
      const e = jsonErr(config.scim.version, pluginName, ctx.status, err, scimType)
      ctx.body = e
      await fetchNotification(ctx, 'onError', caches, verifyTracing)
    }
    endSpan(ctx, span, requestSpan)
    })
  })

  // ==========================================
  //           createUser
  //           createGroup
  // ==========================================
  //
  // POST = /Users
  // Body contains user attributes including userName (userID)
  // Body example:
  // {"active":true,"name":{"familyName":"Elshaug","givenName":"Jarle"},"schemas":["urn:scim:schemas:core:1.0"],"userName":"jael01"}
  //
  // POST = /Groups
  // Body contains group attributes including displayName (group name)
  // Body example:
  // {"displayName":"MyGroup","externalId":"MyExternal","schemas":["urn:scim:schemas:core:1.0"]}
  //
  router.post([`/(|scim/)(!${undefined}|Users|Groups)(|.json)(|.xml)`,
  `/:baseEntity/(|scim/)(!${undefined}|Users|Groups)(|.json)(|.xml)`], async (ctx) => {
    return await TelemetryWrapper(api, async () => {
      requestSpan = verifyTracing(ctx,  'Request')

    let u = ctx.originalUrl.substr(ctx.originalUrl.lastIndexOf('/') + 1) // u = Users<.json|.xml>, Groups<.json|.xml>
    u = u.split('?')[0] // Users?AzureAdScimPatch062020
    const handle = handler[u.split('.')[0]]
    logger.debug(`${gwName}[${pluginName}] [Create ${handle.description}]`)
    let jsonBody = ctx.request.body
    const strBody = JSON.stringify(jsonBody)
    if (strBody === '{}') {
      ctx.status = 500
      let err = new Error('Not accepting empty or none JSON formatted POST requests')
      err = jsonErr(config.scim.version, pluginName, ctx.status, err)
      ctx.body = err
      return
    } else if (handle.createMethod === 'createUser' && !jsonBody.userName && !jsonBody.externalId) {
      ctx.status = 500
      let err = new Error('userName or externalId is mandatory')
      err = jsonErr(config.scim.version, pluginName, ctx.status, err)
      ctx.body = err
      return
    } else if (handle.createMethod === 'createGroup' && !jsonBody.displayName && !jsonBody.externalId) {
      ctx.status = 500
      let err = new Error('displayName or externalId is mandatory')
      err = jsonErr(config.scim.version, pluginName, ctx.status, err)
      ctx.body = err
      return
    }

    logger.debug(`${gwName}[${pluginName}] POST ${ctx.originalUrl} body=${strBody}`)
    jsonBody = JSON.parse(strBody) // using a copy
    const [scimdata, err] = ScimGateway.prototype.convertedScim(jsonBody)
    logger.debug(`${gwName}[${pluginName}] convertedBody=${JSON.stringify(scimdata)}`)
    if (err) {
      ctx.status = 500
      const e = jsonErr(config.scim.version, pluginName, ctx.status, err)
      ctx.body = e
      return
    }
    logger.debug(`${gwName}[${pluginName}] calling "${handle.createMethod}" and awaiting result`)
    delete jsonBody.id // in case included in request
    try {
      const res = await this[handle.createMethod](ctx.params.baseEntity, scimdata, ctx.ctxCopy)
      for (const key in res) { // merge any result e.g: {'id': 'xxxx'}
        jsonBody[key] = res[key]
      }

      if (!jsonBody.id) { // retrieve all attributes including id
        let obj
        try {
          if (handle.createMethod === 'createUser') {
            if (jsonBody.userName) {
              jsonBody.id = jsonBody.userName
              obj = await this[handle.getMethod](ctx.params.baseEntity, { attribute: 'userName', operator: 'eq', value: jsonBody.userName }, [], ctx.ctxCopy)
            } else if (jsonBody.externalId) {
              jsonBody.id = jsonBody.externalId
              obj = await this[handle.getMethod](ctx.params.baseEntity, { attribute: 'externalId', operator: 'eq', value: jsonBody.externalId }, [], ctx.ctxCopy)
            }
          } else if (handle.createMethod === 'createGroup') {
            if (jsonBody.externalId) {
              jsonBody.id = jsonBody.externalId
              obj = await this[handle.getMethod](ctx.params.baseEntity, { attribute: 'externalId', operator: 'eq', value: jsonBody.externalId }, [], ctx.ctxCopy)
            } else if (jsonBody.displayName) {
              jsonBody.id = jsonBody.displayName
              obj = await this[handle.getMethod](ctx.params.baseEntity, { attribute: 'displayName', operator: 'eq', value: jsonBody.displayName }, [], ctx.ctxCopy)
            }
          }
        } catch (err) { }
        if (obj && obj.id) jsonBody = obj
      }

      const location = `${ctx.origin}${ctx.path}/${jsonBody.id}`
      if (!jsonBody.meta) jsonBody.meta = {}
      jsonBody.meta.location = location
      delete jsonBody.password
      jsonBody = addPrimaryAttrs(jsonBody)
      ctx.set('Location', location)
      ctx.status = 201
      ctx.body = jsonBody
      await fetchNotification(ctx, 'onSuccess', caches, verifyTracing)
    } catch (err) {
      let scimType = errorStatus(err, isScimv2, ctx)
      const e = jsonErr(config.scim.version, pluginName, ctx.status, err, scimType)
      ctx.body = e
      await fetchNotification(ctx, 'onError', caches, verifyTracing)
    }
    endSpan(ctx, span, requestSpan)
  })
  }) // post

  // ==========================================
  //           deleteUser
  //           deleteGroup
  // ==========================================
  //
  // DELETE /Users/<id>
  // DELETE /Groups/<id>
  // Note user: using id (not userName). getUsers should therefore set id = userName (userID) e.g. bjensen
  // => We then have: DELETE /Users/bjensen
  // Note groups: using id (not displayName). getGroups should therefore set id = displayName (groupID) e.g. Employees
  // => We then have: DELETE /Groups/Employees
  //
  router.delete([`/(|scim/)(!${undefined}|Users|Groups)/:id`,
  `/:baseEntity/(|scim/)(!${undefined}|Users|Groups)/:id`], async (ctx) => {
    return await TelemetryWrapper(api, async () => {
      requestSpan = verifyTracing(ctx,  'Request')

    let u = ctx.originalUrl.substr(0, ctx.originalUrl.lastIndexOf('/'))
    u = u.substr(u.lastIndexOf('/') + 1) // u = Users, Groups
    const handle = handler[u]
    const id = ctx.params.id
    logger.debug(`${gwName}[${pluginName}] [Delete ${handle.description}] id=${id}`)
    logger.debug(`${gwName}[${pluginName}] calling "${handle.deleteMethod}" and awaiting result`)

    try {
      await this[handle.deleteMethod](ctx.params.baseEntity, id, ctx.ctxCopy)
      ctx.status = 204
      await fetchNotification(ctx, 'onSuccess', caches, verifyTracing)
    } catch (err) {
      let scimType = errorStatus(err, isScimv2, ctx)   
      const e = jsonErr(config.scim.version, pluginName, ctx.status, err)
      ctx.body = e
      await fetchNotification(ctx, 'onError', caches, verifyTracing)
    }
    endSpan(ctx, span, requestSpan)
  })
  }) // delete

  // ==========================================
  //          modifyUser
  //          modifyGroup
  // ==========================================
  //
  // PATCH = /Users/<id>
  // PATCH = /Users/4aa37ddc-4985-4009-ab24-df42d37e2810
  // Note, using id (not userName). getUsers should therefore set id = userName (userID)
  // => We then have: PATCH /Users/bjensen
  //
  // Body contains user attributes to be updated
  // example: {"active":true}
  //
  // Multi-value attributes excluding user attribute 'groups' are customized from array to object based on type
  // This is done for simplifying plugin-code. For more information please see method convertedScim / convertedScim20
  //
  // PATCH = /Groups/<id>
  // PATCH = /Groups/4aa37ddc-4985-4009-ab24-df42d37e2810
  // Note, using id (not displayName). getGroups should therefore set id = displayName
  // => We then have: PATCH = /Groups/Employees
  //
  // Body contains groups attributes to be updated
  // example: {"members":[{"value":"bjensen"}],"schemas":["urn:scim:schemas:core:1.0"]}
  //
  router.patch([`/(|scim/)(!${undefined}|Users|Groups|servicePlans)/:id`,
  `/:baseEntity/(|scim/)(!${undefined}|Users|Groups|servicePlans)/:id`], async (ctx) => {
    return await TelemetryWrapper(api, async () => {
      requestSpan = verifyTracing(ctx,  'Request')
    if (ctx.query.attributes) ctx.query.attributes = ctx.query.attributes.split(',').map(item => item.trim()).join()
    if (ctx.query.excludedAttributes) ctx.query.excludedAttributes = ctx.query.excludedAttributes.split(',').map(item => item.trim()).join()
    let u = ctx.originalUrl.substr(0, ctx.originalUrl.lastIndexOf('/'))
    u = u.substr(u.lastIndexOf('/') + 1) // u = Users, Groups
    const handle = handler[u]
    const id = decodeURIComponent(ctx.params.id)
    const jsonBody = ctx.request.body
    const strBody = JSON.stringify(jsonBody)
    if (strBody === '{}') {
      ctx.status = 500
      let err = new Error('Not accepting empty or none JSON formatted PATCH request')
      err = jsonErr(config.scim.version, pluginName, ctx.status, err)
      ctx.body = err
    } else {
      logger.debug(`${gwName}[${pluginName}] [Modify ${handle.description}] id=${id}`)
      let scimdata, err
      if (jsonBody.Operations) [scimdata, err] = ScimGateway.prototype.convertedScim20(jsonBody) // v2.0
      else [scimdata, err] = ScimGateway.prototype.convertedScim(jsonBody) // v1.1
      logger.debug(`${gwName}[${pluginName}] convertedBody=${JSON.stringify(scimdata)}`)
      if (err) {
        ctx.status = 500
        const e = jsonErr(config.scim.version, pluginName, ctx.status, err)
        ctx.body = e
        return
      }
      logger.debug(`${gwName}[${pluginName}] calling "${handle.modifyMethod}" and awaiting result`)
      try {
        await this[handle.modifyMethod](ctx.params.baseEntity, id, scimdata, ctx.ctxCopy)
        // include full object in response
        if (handle.getMethod !== handler.users.getMethod && handle.getMethod !== handler.groups.getMethod) { // getUsers or getGroups not implemented
          ctx.status = 204
          return
        }
        logger.debug(`${gwName}[${pluginName}] calling "${handle.getMethod}" and awaiting result`)
        const res = await this[handle.getMethod](ctx.params.baseEntity, { attribute: 'id', operator: 'eq', value: id }, ctx.query.attributes ? ctx.query.attributes.split(',').map(item => item.trim()) : [], ctx.ctxCopy)
        scimdata = {
          Resources: [],
          totalResults: null
        }
        if (res) {
          if (res.Resources && Array.isArray(res.Resources)) {
            scimdata.Resources = res.Resources
            scimdata.totalResults = res.totalResults
          } else if (Array.isArray(res)) scimdata.Resources = res
          else if (typeof (res) === 'object' && Object.keys(res).length > 0) scimdata.Resources[0] = res
        }
        if (scimdata.Resources.length !== 1) throw new Error(`using ${handle.getMethod} to retrive user ${id} after ${handle.modifyMethod} but response did not include user object`)
        const location = ctx.origin + ctx.path
        ctx.set('Location', location)
        scimdata.Resources[0] = addPrimaryAttrs(scimdata.Resources[0])
        scimdata = utils.stripObj(scimdata.Resources[0], ctx.query.attributes, ctx.query.excludedAttributes)
        scimdata = addSchemas(scimdata, handle.description, isScimv2)
        ctx.status = 200
        ctx.body = scimdata
        await fetchNotification(ctx, 'onSuccess', caches, verifyTracing, ScimGateway.prototype.convertedScim20(ctx.request.body))
      } catch (err) {
        let scimType = errorStatus(err, isScimv2, ctx)
        const e = jsonErr(config.scim.version, pluginName, ctx.status, err, scimType)
        ctx.body = e
        await fetchNotification(ctx, 'onError', caches, verifyTracing, ScimGateway.prototype.convertedScim20(ctx.request.body))
      }
    }
    endSpan(ctx, span, requestSpan)
  })
  }) // patch

  // ==========================================
  //          REPLACE USER
  //          REPLACE GROUP
  // ==========================================
  router.put([`/(|scim/)(!${undefined}|Users|Groups|servicePlans)/:id`,
  `/:baseEntity/(|scim/)(!${undefined}|Users|Groups|servicePlans)/:id`], async (ctx) => {
    return await TelemetryWrapper(api, async () => {
      requestSpan = verifyTracing(ctx,  'Request')

    let u = ctx.originalUrl.substr(0, ctx.originalUrl.lastIndexOf('/'))
    u = u.substr(u.lastIndexOf('/') + 1) // u = Users, Groups
    const handle = handler[u]
    const id = ctx.params.id
    const jsonBody = ctx.request.body
    const strBody = JSON.stringify(jsonBody)
    if (strBody === '{}') {
      ctx.status = 500
      let err = new Error('Not accepting empty or none JSON formatted PUT requests')
      err = jsonErr(config.scim.version, pluginName, ctx.status, err)
      ctx.body = err
    } else {
      logger.debug(`${gwName}[${pluginName}] PUT ${ctx.originalUrl} body=${strBody}`)
      try {
        // get current object
        logger.debug(`${gwName}[${pluginName}] calling "${handle.getMethod}" and awaiting result`)
        let res = await this[handle.getMethod](ctx.params.baseEntity, { attribute: 'id', operator: 'eq', value: id }, [], ctx.ctxCopy)

        let currentObj = {}
        if (res && res.Resources && Array.isArray(res.Resources) && res.Resources.length === 1) currentObj = res.Resources[0]
        else if (Array.isArray(res) && res.length === 1) currentObj = res[0]
        else if (res && typeof (res) === 'object' && Object.keys(res).length > 0) currentObj = res
        else throw Error(`put using method ${handle.getMethod} got unexpected response: ${JSON.stringify(res)}`)

        const clearedObj = clearObjectValues(currentObj)
        delete clearedObj.active
        delete clearedObj.password
        delete clearedObj.meta

        // usePutSoftSync=true prevents removing existing roles (only add roles)
        if (config.scim.usePutSoftSync) {
          if (clearedObj.roles && Array.isArray(clearedObj.roles)) {
            for (let i = 0; i < clearedObj.roles.length; i++) {
              if (clearedObj.roles[i].operation && clearedObj.roles[i].operation === 'delete') {
                clearedObj.roles.splice(i, 1) // delete
                i -= 1
              }
            }
          }
        }

        // merge cleared object with the new
        const newObj = utils.extendObj(clearedObj, jsonBody)
        delete newObj.id
        delete newObj.userName
        delete newObj.externalId
        delete newObj.groups // do not support "group member of users"
        delete newObj.schemas
        delete newObj.meta
        if (handle.getMethod === handler.groups.getMethod) delete newObj.displayName

        let [scimdata, err] = ScimGateway.prototype.convertedScim(newObj)
        if (err) throw err

        // update object
        logger.debug(`${gwName}[${pluginName}] calling "${handle.modifyMethod}" and awaiting result`)
        await this[handle.modifyMethod](ctx.params.baseEntity, id, scimdata, ctx.ctxCopy)

        // add/remove groups
        if (jsonBody.groups && Array.isArray(jsonBody.groups)) { // only if groups included, { "groups": [] } will remove all existing
          if (typeof this[handler.groups.getMethod] !== 'function' || typeof this[handler.groups.modifyMethod] !== 'function') {
            throw new Error('replaceUser error: put operation can not be fully completed for the user`s groups, methods like getGroups() and modifyGroup() are not implemented')
          }
          let currentGroups
          if (currentObj.groups && Array.isArray(currentObj.groups)) currentGroups = currentObj.groups
          else { // try to get current groups the standard way
            let res
            try {
              res = await this[handler.groups.getMethod](ctx.params.baseEntity, { attribute: 'members.value', operator: 'eq', value: decodeURIComponent(id) }, ['id', 'displayName'], ctx.ctxCopy)
            } catch (err) {} // method may be implemented but throwing error like groups not supported/implemented
            currentGroups = []
            if (res && res.Resources && Array.isArray(res.Resources) && res.Resources.length > 0) {
              for (let i = 0; i < res.Resources.length; i++) {
                if (!res.Resources[i].id) continue
                const el = {}
                el.value = res.Resources[i].id
                if (res.Resources[i].displayName) el.display = res.Resources[i].displayName
                currentGroups.push(el) // { "value": "Admins", "display": "Admins"}
              }
            }
          }
          currentGroups = currentGroups.map((el) => {
            if (el.value) {
              el.value = decodeURIComponent(el.value)
            }
            return el
          })

          const addGrps = []
          const removeGrps = []
          // add
          for (let i = 0; i < jsonBody.groups.length; i++) {
            if (!jsonBody.groups[i].value) continue
            jsonBody.groups[i].value = decodeURIComponent(jsonBody.groups[i].value)
            let found = false
            for (let j = 0; j < currentGroups.length; j++) {
              if (jsonBody.groups[i].value === currentGroups[j].value) {
                found = true
                break
              }
            }
            if (!found && jsonBody.groups[i].value) addGrps.push(jsonBody.groups[i].value)
          }
          // remove
          for (let i = 0; i < currentGroups.length; i++) {
            let found = false
            for (let j = 0; j < jsonBody.groups.length; j++) {
              if (!jsonBody.groups[j].value) continue
              jsonBody.groups[j].value = decodeURIComponent(jsonBody.groups[j].value)
              if (currentGroups[i].value === jsonBody.groups[j].value) {
                found = true
                break
              }
            }
            if (!found && currentGroups[i].value) removeGrps.push(currentGroups[i].value)
          }

          const addGroups = async (grp) => {
            const obj = { members: [{ value: id }] }
            return await this[handler.groups.modifyMethod](ctx.params.baseEntity, grp, obj, ctx.ctxCopy)
          }

          const removeGroups = async (grp) => {
            const obj = { members: [{ operation: 'delete', value: id }] }
            return await this[handler.groups.modifyMethod](ctx.params.baseEntity, grp, obj, ctx.ctxCopy)
          }

          let errRemove
          if (!config.scim.usePutSoftSync) { // default will remove any existing groups not included, usePutSoftSync=true prevents removing existing groups (only add groups)
            await Promise.all(removeGrps.map((grp) => removeGroups(grp)))
              .then()
              .catch((err) => {
                errRemove = err
              })
          }

          let errAdd
          await Promise.all(addGrps.map((grp) => addGroups(grp)))
            .then()
            .catch((err) => {
              errAdd = err
            })

          let errMsg = ''
          if (errRemove) errMsg = `removeGroups error: ${errRemove.message}`
          if (errAdd) errMsg += `${errMsg ? ' ' : ''}addGroups error: ${errAdd.message}`
          if (errMsg) throw new Error(errMsg)
        }

        // get updated object
        logger.debug(`${gwName}[${pluginName}] calling "${handle.getMethod}" and awaiting result`)
        res = await this[handle.getMethod](ctx.params.baseEntity, { attribute: 'id', operator: 'eq', value: id }, [], ctx.ctxCopy)

        scimdata = {}
        if (res && res.Resources && Array.isArray(res.Resources) && res.Resources.length === 1) scimdata = res.Resources[0]
        else if (Array.isArray(res) && res.length === 1) scimdata = res[0]
        else if (res && typeof (res) === 'object' && Object.keys(res).length > 0) scimdata = res
        else throw Error(`put using method ${handle.getMethod} got unexpected response: ${JSON.stringify(res)}`)

        // include groups
        if (handle.getMethod === handler.users.getMethod && typeof this[handler.groups.getMethod] === 'function') {
          logger.debug(`${gwName}[${pluginName}] calling "${handler.groups.getMethod}" and awaiting result`)
          const res = await this[handler.groups.getMethod](ctx.params.baseEntity, { attribute: 'members.value', operator: 'eq', value: id }, ['id', 'displayName'], ctx.ctxCopy)
          let grps = []
          if (res && res.Resources && Array.isArray(res.Resources)) grps = res.Resources
          else if (Array.isArray(res)) grps = res
          else if (res && typeof (res) === 'object' && Object.keys(res).length > 0) grps = [res]
          else throw Error(`put using method ${handler.groups.getMethod} got unexpected response: ${JSON.stringify(res)}`)

          if (grps.length > 0) {
            scimdata.groups = []
            for (let i = 0; i < grps.length; i++) {
              const el = {}
              el.value = grps[i].id
              if (grps[i].displayName) el.display = grps[i].displayName
              if (isScimv2) el.type = 'direct'
              else el.type = { value: 'direct' }
              if (el.value) scimdata.groups.push(el) // { "value": "Admins", "display": "Admins", "type": "direct"}
            }
          }
        }

        const location = ctx.origin + ctx.path
        ctx.set('Location', location)
        scimdata = addSchemas(scimdata, handle.description, isScimv2)
        ctx.status = 200
        ctx.body = scimdata
        await fetchNotification(ctx, 'onSuccess', caches, verifyTracing)
      } catch (err) {
        let scimType = errorStatus(err, isScimv2, ctx)
        const e = jsonErr(config.scim.version, pluginName, ctx.status, err)
        ctx.body = e
        await fetchNotification(ctx, 'onError', caches, verifyTracing)
      }
    }
    endSpan(ctx, span, requestSpan)
  })
  })


  // ==========================================
  // Starting up...
  // ==========================================

  for (let i = 0; i < logger.transports.length; i++) { // loglevel=off => turn off logging
    if (logger.transports[i].name === 'file' && config.log.loglevel.file && config.log.loglevel.file.toLowerCase() === 'off') {
      logger.transports[i].silent = true
    } else if (logger.transports[i].name === 'console' && config.log.loglevel.console && config.log.loglevel.console.toLowerCase() === 'off') {
      logger.transports[i].silent = true
    }
  }

  logger.info('===================================================================')

  if (config.localhostonly === true) {
    logger.info(`${gwName}[${pluginName}] denying other clients than localhost (127.0.0.1)`)
    if (config.certificate && config.certificate.key && config.certificate.cert) {
      // SSL
      server = https.createServer({
        key: fs.readFileSync(configDir + '/certs/' + config.certificate.key),
        cert: fs.readFileSync(configDir + '/certs/' + config.certificate.cert)
      }, app.callback()).listen(config.port, 'localhost')
      logger.info(`${gwName}[${pluginName}] now listening SCIM ${config.scim.version} on TLS port ${config.port}...\n`)
    } else if (config.certificate && config.certificate.pfx && config.certificate.pfx.bundle) {
      // SSL using PFX / PKCS#12
      server = https.createServer({
        pfx: fs.readFileSync(configDir + '/certs/' + config.certificate.pfx.bundle),
        passphrase: pwPfxPassword
      }, app.callback()).listen(config.port, 'localhost')
      logger.info(`${gwName}[${pluginName}] now listening SCIM ${config.scim.version} on TLS port ${config.port}...\n`)
    } else {
      // none SSL
      server = http.createServer(app.callback()).listen(config.port, 'localhost')
      logger.info(`${gwName}[${pluginName}] now listening SCIM ${config.scim.version} on port ${config.port}...\n`)

    }
  } else {
    logger.info(`${gwName}[${pluginName}] accepting requests from all clients`)
    if (config.certificate && config.certificate.key && config.certificate.cert) {
      // SSL self signed cert e.g: openssl req -nodes -newkey rsa:2048 -x509 -sha256 -days 3650 -keyout key.pem -out cert.pem -subj "/O=NodeJS/OU=Testing/CN=<FQDN>"
      // Note, self signed certificate (cert.pem) also needs to be imported at the CA Connector Server
      server = https.createServer({
        key: fs.readFileSync(configDir + '/certs/' + config.certificate.key),
        cert: fs.readFileSync(configDir + '/certs/' + config.certificate.cert),
        ca: (config.certificate.ca) ? fs.readFileSync(configDir + '/certs/' + config.certificate.ca) : null
      }, app.callback()).listen(config.port)
      logger.info(`${gwName}[${pluginName}] now listening SCIM ${config.scim.version} on TLS port ${config.port}...\n`)
    } else if (config.certificate && config.certificate.pfx && config.certificate.pfx.bundle) {
      // SSL using PFX / PKCS#12
      server = https.createServer({
        pfx: fs.readFileSync(configDir + '/certs/' + config.certificate.pfx.bundle),
        passphrase: pwPfxPassword
      }, app.callback()).listen(config.port)
      logger.info(`${gwName}[${pluginName}] now listening SCIM ${config.scim.version} on TLS port ${config.port}...\n`)
    } else {
      // none SSL
      server = http.createServer(app.callback()).listen(config.port)
      logger.info(`${gwName}[${pluginName}] now listening SCIM ${config.scim.version} on port ${config.port}...\n`)
    }
  }

  function onSignal () {
    logger.info('server is starting cleanup')
    return Promise.all([
      // your clean logic, like closing database connections
    ])
  }

  function onShutdown () {
    logger.info('cleanup finished, server is shutting down')
  }

  function beforeShutdown () {
    return new Promise(resolve => {
      setTimeout(resolve, config.kubernetes.shutdownTimeout || 15000)
    })
  }

  function healthCheck () {
    return Promise.resolve(
      // optionally include a resolve value to be included as
      // info in the health check response
    )
  }
  const options = {
    // health check options
    healthChecks: {
      '/healthcheck': healthCheck, // a function returning a promise indicating service health,
      verbatim: true // [optional = false] use object returned from /healthcheck verbatim in response
    },

    // cleanup options
    timeout: config.kubernetes.forceExitTimeout || 1000, // [optional = 1000] number of milliseconds before forceful exiting
    beforeShutdown, // [optional] called before the HTTP server starts its shutdown
    onSignal, // [optional] cleanup function, returning a promise (used to be onSigterm)
    onShutdown // [optional] called right before exiting
  }

  if (config.kubernetes.enabled) createTerminus(server, options)

  // set loglevel according to config
  const arrValidLevel = ['silly', 'debug', 'verbose', 'info', 'warn', 'error']
  for (let i = 0; i < logger.transports.length; i++) {
    if (logger.transports[i].name === 'file') config.log.loglevel.file && arrValidLevel.includes(config.log.loglevel.file.toLowerCase()) ? logger.transports[i].level = config.log.loglevel.file : logger.transports[i].level = 'debug'
    else if (logger.transports[i].name === 'console') config.log.loglevel.console && arrValidLevel.includes(config.log.loglevel.console.toLowerCase()) ? logger.transports[i].level = config.log.loglevel.console : logger.transports[i].level = 'debug'
  }

  log.emailOnError = async (msg) => { // sending mail on error
    if (!config.emailOnError || !config.emailOnError.smtp || !(config.emailOnError.smtp.enabled === true) || isMailLock) return null // not sending mail
    isMailLock = true

    setTimeout(function () { // release lock after "sendInterval" minutes
      isMailLock = false
    }, (config.emailOnError.smtp.sendInterval || 15) * 1000 * 60)

    const bodyHtml = `<html><body> 
          <p>${msg}</p> 
          <br> 
          <p><strong>This is an automatically generated email - please do NOT reply to this email or forward to others</strong></p> 
          </body></html>`

    const smtpConfig = {
      host: config.emailOnError.smtp.host, // e.g. smtp.office365.com
      port: config.emailOnError.smtp.port || 587,
      proxy: config.emailOnError.smtp.proxy || null,
      secure: (config.emailOnError.smtp.port === 465), // false on 25/587
      tls: { ciphers: 'TLSv1.2' }
    }
    if (config.emailOnError.smtp.authenticate) {
      smtpConfig.auth = {}
      smtpConfig.auth.user = config.emailOnError.smtp.username
      smtpConfig.auth.pass = config.emailOnError.smtp.password
    }

    const transporter = nodemailer.createTransport(smtpConfig)
    const mailOptions = {
      from: config.emailOnError.smtp.username, // sender address
      to: config.emailOnError.smtp.to, // list of receivers - comma separated
      cc: config.emailOnError.smtp.cc,
      subject: 'ScimGateway error message',
      html: bodyHtml // 'text': bodyText
    }

    transporter.sendMail(mailOptions, function (err, info) {
      if (err) logger.error(`${gwName}[${pluginName}] mailOnError sending failed: ${err.message}`)
      else logger.debug(`${gwName}[${pluginName}] mailOnError sent to: ${config.emailOnError.smtp.to}${(config.emailOnError.smtp.cc) ? ',' + config.emailOnError.smtp.cc : ''}`)
    })
    return null
  } // emailOnError

  const gracefulShutdown = function () {
    logger.debug(`${gwName}[${pluginName}] received terminate/kill signal - closing connections and exit`)
    for (let i = logger.transports.length - 1; i >= 0; i--) { // enable info logging
      try { logger.transports[i].level = 'info' } catch (e) { }
    }
    logger.info(`${gwName}[${pluginName}] pheww... ${requestCounter} requests have been processed in the period ${startTime} - ${utils.timestamp()}\n`)
    logger.close()
    server.close(function () {
      setTimeout(function () { // plugins may also use SIGTERM/SIGINT
        process.exit(0)
      }, 0.5 * 1000)
    })
    setTimeout(function () { // problem closing server connections in time due to keep-alive sessions (active browser connection?), now forcing exit
      process.exit(1)
    }, 2 * 1000)
  }

  process.on('unhandledRejection', (err) => { // older versions of V8, unhandled promise rejections are silently dropped
    logger.error(`${gwName}[${pluginName}] Async function with unhandledRejection: ${err.stack}`)
  })
  process.once('SIGTERM', gracefulShutdown) // kill (windows subsystem lacks signaling support for process.kill)
  process.once('SIGINT', gracefulShutdown) // Ctrl+C

  //
  // exported methods inside ScimGateway because of local defined variable multiValueTypes
  //
  ScimGateway.prototype.isMultiValueTypes = function isMultiValueTypes (attr) { // emails
    return multiValueTypes.includes(attr)
  }

  // Multi-value attributes are customized from array to object based on type
  // except: groups, members and roles
  // e.g "emails":[{"value":"bjensen@example.com","type":"work"}] => {"emails": {"work": {"value":"bjensen@example.com","type":"work"}}}
  // Cleared values are set as user attributes with blank value ""
  // e.g {meta:{attributes:['name.givenName','title']}} => {"name": {"givenName": ""}), "title": ""}
  ScimGateway.prototype.convertedScim = function convertedScim (obj) {
    let err = null
    const scimdata = utils.copyObj(obj)
    if (scimdata.schemas) delete scimdata.schemas
    const newMulti = {}
    for (const key in scimdata) {
      if (Array.isArray(scimdata[key]) && (scimdata[key].length > 0)) {
        if (key === 'groups' || key === 'members' || key === 'roles') {
          scimdata[key].forEach(function (element, index) {
            if (element.value) scimdata[key][index].value = decodeURIComponent(element.value)
          })
        } else if (multiValueTypes.includes(key)) { // "type converted object" // groups, roles, member and scim.excludeTypeConvert are not included
          const tmpAddr = []
          scimdata[key].forEach(function (element, index) {
            if (!element.type) element.type = 'undefined' // "none-type"
            if (element.operation && element.operation === 'delete') { // add as delete if same type not included as none delete
              const arr = scimdata[key].filter(obj => obj.type && obj.type === element.type && !obj.operation)
              if (arr.length < 1) {
                if (!newMulti[key]) newMulti[key] = {}
                if (newMulti[key][element.type]) {
                  if (['addresses'].includes(key)) { // not checking type, but the others have to be unique
                    for (const i in element) {
                      if (i !== 'type') {
                        if (tmpAddr.includes(i)) {
                          err = new Error(`'type converted object' ${key} - includes more than one element having same ${i}, or ${i} is blank on more than one element - note, setting configuration scim.skipTypeConvert=true will disable this logic/check`)
                        }
                        tmpAddr.push(i)
                      }
                    }
                  } else {
                    err = new Error(`'type converted object' ${key} - includes more than one element having same type, or type is blank on more than one element - note, setting configuration scim.skipTypeConvert=true will disable this logic/check`)
                  }
                }
                newMulti[key][element.type] = {}
                for (const i in element) {
                  newMulti[key][element.type][i] = element[i]
                }
                newMulti[key][element.type].value = '' // delete
              }
            } else {
              if (!newMulti[key]) newMulti[key] = {}
              if (newMulti[key][element.type]) {
                if (['addresses'].includes(key)) { // not checking type, but the others have to be unique
                  for (const i in element) {
                    if (i !== 'type') {
                      if (tmpAddr.includes(i)) {
                        err = new Error(`'type converted object' ${key} - includes more than one element having same ${i}, or ${i} is blank on more than one element - note, setting configuration scim.skipTypeConvert=true will disable this logic/check`)
                      }
                      tmpAddr.push(i)
                    }
                  }
                } else {
                  err = new Error(`'type converted object' ${key} - includes more than one element having same type, or type is blank on more than one element - note, setting configuration scim.skipTypeConvert=true will disable this logic/check`)
                }
              }
              newMulti[key][element.type] = {}
              for (const i in element) {
                newMulti[key][element.type][i] = element[i]
              }
            }
          })
          delete scimdata[key]
        }
      }
    }
    if (scimdata.active && typeof scimdata.active === 'string') {
      const lcase = scimdata.active.toLowerCase()
      if (lcase === 'true') scimdata.active = true
      else if (lcase === 'false') scimdata.active = false
    }
    if (scimdata.meta) { // cleared attributes e.g { meta: { attributes: [ 'name.givenName', 'title' ] } }
      if (Array.isArray(scimdata.meta.attributes)) {
        scimdata.meta.attributes.forEach(el => {
          let rootKey
          let subKey
          if (el.startsWith('urn:')) { // can't use dot.str on key having dot e.g. urn:ietf:params:scim:schemas:extension:enterprise:2.0:User:department
            const i = el.lastIndexOf(':')
            subKey = el.substring(i + 1)
            if (subKey === 'User' || subKey === 'Group') rootKey = el
            else rootKey = el.substring(0, i)
          }
          if (rootKey) {
            if (!scimdata[rootKey]) scimdata[rootKey] = {}
            dot.str(subKey, '', scimdata[rootKey])
          } else {
            dot.str(el, '', scimdata)
          }
        })
      }
      delete scimdata.meta
    }
    for (const key in newMulti) {
      dot.copy(key, key, newMulti, scimdata)
    }
    return [scimdata, err]
  }
} // scimgateway

//
// exported methods
//
ScimGateway.prototype.countries = countries

ScimGateway.prototype.getPassword = (pwEntity, configFile) => {
  return utils.getPassword(pwEntity, configFile) // utils.getPassword('scimgateway.password', './config/plugin-testmode.json');
}

ScimGateway.prototype.formatError = (action, err) => {
  throw  new Error(`${action} error: ${err.message}`);
}

ScimGateway.prototype.timestamp = () => {
  return utils.timestamp()
}

ScimGateway.prototype.copyObj = (o) => {
  return utils.copyObj(o)
}

ScimGateway.prototype.extendObj = (obj, src) => {
  return utils.extendObj(obj, src)
}

ScimGateway.prototype.Lock = utils.Lock

ScimGateway.prototype.getArrayObject = (Obj, element, type) => {
  if (Obj[element]) { // element is case sensitive
    return Obj[element].find(function (el) {
      return (el.type && (el.type).toLowerCase() === type.toLowerCase())
    })
  }
  return null
}

/*
ScimGateway.prototype.isMultiValueTypes = function isMultiValueTypes (attr) { // emails
  return multiValueTypes.includes(attr)
}
*/

//
// getMultivalueTypes returns an array of mulitvalue attributes allowing type e.g [emails,addresses,...]
// objName should be 'User' or 'Group'
//
const getMultivalueTypes = (objName, scimDef) => { // objName = 'User' or 'Group'
  if (!objName) return []

  const obj = scimDef.Schemas.Resources.find(el => {
    return (el.name === objName)
  })
  if (!obj) return []

  return obj.attributes
    .filter(el => {
      return (el.multiValued === true && el.subAttributes &&
        el.subAttributes
          .find(function (subel) {
            return (subel.name === 'type')
          })
      )
    })
    .map(obj => obj.name)
}

// config can be set based on environment variables
// config can be set based on correspondig json-content in external file (supports also dot notation)
// syntax environment = "process.env.<ENVIRONMENT>" e.g. config.port could have value "process.env.PORT", then using environment variable PORT
// syntax file = "process.file.<PATH>" e.g. config.password could have value "process.file./tmp/myconf.json"
ScimGateway.prototype.processExtConfig = function processExtConfig (pluginName, config, isMain) {
  const processEnv = 'process.env.'
  const processFile = 'process.file.'
  const processText = 'process.text.'
  const dotConfig = dot.dot(config)
  const processTexts = new Map()
  const processFiles = new Map()

  for (const key in dotConfig) {
    let value = dotConfig[key]
    if (value && value.constructor === String && value.includes(processEnv)) {
      const envKey = value.substring(processEnv.length)
      value = process.env[envKey]
      dotConfig[key] = value
      if (!value) {
        const newErr = new Error(`configuration failed - can't use none existing environment: "${envKey}"`)
        newErr.name = 'processExtConfig'
        throw newErr
      }
    } else if (value && value.constructor === String && value.includes(processText)) {
      const filePath = value.substring(processText.length)
      try {
        if (!processTexts.has(filePath)) { // avoid reading previous file
          processTexts.set(filePath, fs.readFileSync(filePath, 'utf8'))
        }
        value = processTexts.get(filePath) // directly a string
      } catch (err) {
        value = undefined
        throw new Error(`configuration failed - can't read text from external file: "${filePath}"`)
      }
      dotConfig[key] = value
    } else if (value && value.constructor === String && value.includes(processFile)) {
      const filePath = value.substring(processFile.length)
      try {
        if (!processFiles.has(filePath)) { // avoid reading previous file
          processFiles.set(filePath, JSON.parse(fs.readFileSync(filePath, 'utf8')))
        }
        try {
          const jContent = processFiles.get(filePath) // json or json-dot-notation formatting is supported
          const dotContent = dot.dot(dot.object(jContent))
          let newKey = null
          if (isMain) newKey = `${pluginName}.scimgateway.${key}`
          else newKey = `${pluginName}.endpoint.${key}`
          value = dotContent[newKey]
          if (value === undefined) {
            if (dotContent[newKey + '.0']) { // check if array
              let i = 0
              do {
                dotConfig[key + '.' + i] = dotContent[newKey + '.' + i]
                i += 1
              } while (dotContent[newKey + '.' + i])
            } else {
              const newErr = new Error(`configuration failed - external JSON file "${filePath}" does not contain key: "${newKey}"`)
              newErr.name = 'processExtConfig'
              throw newErr
            }
          }
        } catch (err) {
          if (err.name && err.name === 'processExtConfig') throw err
          else {
            const newErr = new Error(`configuration failed - can't JSON parse external file: "${filePath}"`)
            newErr.name = 'processExtConfig'
            throw newErr
          }
        }
      } catch (err) {
        value = undefined
        if (err.name && err.name === 'processExtConfig') throw err
        else throw (new Error(`configuration failed - can't read external configuration file: ${err.message}`))
      }
      dotConfig[key] = value
    }
  }
  processTexts.clear()
  processFiles.clear()
  return dot.object(dotConfig)
}

// SCIM/CustomScim <=> endpoint attribute parsing used by plugins
// returns [object/string, err]
// TO-DO: rewrite and simplify...
ScimGateway.prototype.endpointMapper = async function endpointMapper (direction, parseObj, mapObj) {
  const dotMap = dot.dot(mapObj)
  let str = ''
  let isObj = false
  let noneCore = false
  const arrUnsupported = []
  const inboundArrCheck = []
  const complexArr = []
  const complexObj = {
    addresses: {},
    emails: {},
    phoneNumbers: {},
    entitlements: {},
    ims: {},
    photos: {}
    // roles: {} using array
  }
  let dotParse = null
  const dotNewObj = {}

  if (parseObj.constructor === String || parseObj.constructor === Array) str = parseObj // parseObj is attributes list e.g. 'userName,id' or ['userName', 'id']
  else {
    isObj = true
    if (parseObj['@odata.context']) delete parseObj['@odata.context'] // AAD cleanup  
    if (parseObj.controls) delete parseObj.controls // Active Directory cleanup
    dotParse = dot.dot(parseObj) // {"name": {"givenName": "myName"}} => {"name.givenName": "myName"}

    // deletion of complex entry => set to blank
    const arrDelete = []
    for (const key in dotParse) {
      if (key.endsWith('.operation')) {
        const arr = key.split('.') // addresses.work.operation
        if (arr.length > 2 && complexObj[arr[0]] && dotParse[key] === 'delete') {
          arrDelete.push(`${arr[0]}.${arr[1]}.`) // addresses.work.
          delete dotParse[key]
        }
      }
    }
    for (let i = 0; i < arrDelete.length; i++) {
      for (const key in dotParse) {
        if (key.startsWith(arrDelete[i])) dotParse[key] = '' // Active Directory: if country included, no logic on country codes cleanup - c (shortname) and countryCode
      }
    }
  }

  switch (direction) {
    case 'outbound':
      for(const mapKey in mapObj){
        // formatting mapping variables
        if(mapObj[mapKey].type === 'dateTime' && parseObj[mapObj[mapKey].mapTo]){
          dotParse[mapObj[mapKey].mapTo] = new Date(parseObj[mapObj[mapKey].mapTo])
        }
        
        let deafultValue = mapObj[mapKey].default
        if(![undefined, null, ""].includes(deafultValue)){           
          let expression = jsonata(deafultValue);
          let result = await expression.evaluate(parseObj) || '';
          if(result.toString().trim().length && !dotParse[mapObj[mapKey].mapTo]) {
            dotParse[mapObj[mapKey].mapTo] = result
          }
        }
      }
      if (isObj) { // body (patch/put)
        for (let key in dotParse) {
          let found = false
          let arrIndex = null
          const arr = key.split('.') // multivalue/array - servicePlan.0.value
          const keyOrg = key
          if (arr[arr.length - 1] === 'value') {
            if (!isNaN(arr[arr.length - 2])) { // servicePlan.0.value => servicePlan.0
              for (let i = 0; i < (arr.length - 2); i++) {
                if (i === 0) key = arr[i]
                else key += `.${arr[i]}`
              }
              arrIndex = arr[arr.length - 2]
            } else if (arr[arr.length - 2].slice(-1) === ']' && arr.length - 2 === 0) { // groups[0].value => groups.value
              const startPos = arr[0].indexOf('[')
              if (startPos > 0) {
                key = arr[0].substring(0, startPos) + '.value' // groups.value
                arrIndex = arr[0].substring(startPos + 1, arr[0].length - 1) // 1
              }
            }
          }
          for (const key2 in dotMap) {
            if (!key2.endsWith('.mapTo')) continue
            if (dotMap[key2].split(',').map(item => item.trim().toLowerCase()).includes(key.toLowerCase())) {
              found = true
              const keyRoot = key2.split('.').slice(0, -1).join('.') // xx.yy.mapTo => xx.yy
              if (dotMap[`${keyRoot}.type`] === 'array' && arrIndex && arrIndex >= 0) {
                dotNewObj[`${keyRoot}.${arrIndex}`] = dotParse[keyOrg] // servicePlan.0.value => servicePlan.0 and groups[0].value => memberOf.0
              }
              dotNewObj[keyRoot] = dotParse[key] // {"accountEnabled": {"mapTo": "active"} => str.replace("accountEnabled", "active")
              break
            }
          }
          if (!found) arrUnsupported.push(key)
        }
      } else { // string (get)
        const resArr = []
        let strArr = []
        if (Array.isArray(str)) {
          for (let i = 0; i < str.length; i++) {
            strArr = strArr.concat(str[i].split(',').map(item => item.trim())) // supports "id,userName" e.g. {"mapTo": "id,userName"}
          }
        } else strArr = str.split(',').map(item => item.trim())
        for (let i = 0; i < strArr.length; i++) {
          const attr = strArr[i]
          let found = false
          for (const key in dotMap) {
            if (!key.endsWith('.mapTo')) continue
            const keyNotDot = key.substring(0, key.indexOf('.mapTo'))
            if (dotMap[key].split(',').map(item => item.trim()).includes(attr)) { // supports { "mapTo": "userName,id" }
              found = true
              if (!resArr.includes(keyNotDot)) resArr.push(keyNotDot)
              break
            } else if (attr === 'roles' && dotMap[key] === 'roles.value') { // allow get using attribute roles - convert to correct roles.value
              found = true
              resArr.push(keyNotDot)
              break
            } else {
              if (dotMap[key].startsWith(attr + '.')) { // e.g. emails - complex definition
                if (complexObj[attr]) {
                  found = true
                  resArr.push(keyNotDot)
                // don't break - check for multiple complex definitions
                }
              }
            }
          }
          if (!found) {
            arrUnsupported.push(attr) // comment out? - let caller decide if not to handle unsupported on GET requests (string)
          }
        }
        if (Array.isArray(str)) str = resArr
        else str = resArr.toString()
      }
      break

    case 'inbound':
      for (let key in dotParse) {
        if (Array.isArray(dotParse[key]) && dotParse[key].length < 1) continue // avoid including 'value' in empty array if mapTo xx.value

        if (key.startsWith('lastLogon') && !isNaN(dotParse[key])) { // Active Directory date convert e.g. 132340394347050132 => "2020-05-15 20:03:54"
          const ll = new Date(parseInt(dotParse[key], 10) / 10000 - 11644473600000)
          dotParse[key] = ll.getFullYear() + '-' +
            ('00' + (ll.getMonth() + 1)).slice(-2) + '-' +
            ('00' + ll.getDate()).slice(-2) + ' ' +
            ('00' + (ll.getHours())).slice(-2) + ':' +
            ('00' + ll.getMinutes()).slice(-2) + ':' +
            ('00' + ll.getSeconds()).slice(-2)
        }

        // first element array gives xxx[0] instead of xxx.0
        let keyArr = key.split('.')
        if (keyArr[0].slice(-1) === ']') { // last character=]
          let newStr = keyArr[0]
          newStr = newStr.replace('[', '.')
          newStr = newStr.replace(']', '') // member[0] => member.0
          dotParse[newStr] = dotParse[key]
          key = newStr // will be handled below
        }

        let dotArrIndex = null
        keyArr = key.split('.')
        if (keyArr.length > 1 && !isNaN(keyArr[1])) { // array
          key = keyArr[0] // "proxyAddresses.0" => "proxyAddresses"
          dotArrIndex = keyArr[1]
        }

        if (!dotMap[`${key}.mapTo`]) continue

        if (dotMap[`${key}.type`] === 'array') {
          let newStr = dotMap[`${key}.mapTo`]
          if (newStr === 'roles') { // {"mapTo": "roles"} should be {"mapTo": "roles.value"}
            arrUnsupported.push('roles.value')
          }
          let multiValue = true
          if (newStr.indexOf('.value') > 0) newStr = newStr.substring(0, newStr.indexOf('.value')) // multivalue back to ScimGateway - remove .value if defined
          else multiValue = false
          if (dotArrIndex !== null) { // array e.g proxyAddresses.value mapTo proxyAddresses converts proxyAddresses.0 => proxyAddresses.0.value
            if (multiValue) dotNewObj[`${newStr}.${dotArrIndex}.value`] = dotParse[`${key}.${dotArrIndex}`]
            else {
              if (dotMap[`${key}.typeInbound`] && dotMap[`${key}.typeInbound`] === 'string') {
                if (!dotNewObj[newStr]) dotNewObj[newStr] = dotParse[`${key}.${dotArrIndex}`]
                else dotNewObj[newStr] = `${dotNewObj[newStr]}, ${dotParse[`${key}.${dotArrIndex}`]}`
              } else dotNewObj[`${newStr}.${dotArrIndex}`] = dotParse[`${key}.${dotArrIndex}`]
            }
          } else { // type=array but element is not array
            if (multiValue) dotNewObj[`${newStr}.0.value`] = dotParse[key]
            else dotNewObj[newStr] = dotParse[key]
            if (!inboundArrCheck.includes(newStr)) inboundArrCheck.push(newStr) // will be checked
          }
        } else { // none array
          // let mapTo = mapObj[key].mapTo
          let mapTo = dotMap[`${key}.mapTo`]
          if (mapTo.startsWith('urn:')) { // dot workaround for none core (e.g. enterprise and custom schema attributes) having dot in key e.g "2.0": urn:ietf:params:scim:schemas:extension:enterprise:2.0:User.department
            mapTo = mapTo.replace('.', '##') // only first occurence
            noneCore = true
          }
          const arrMapTo = mapTo.split(',').map(item => item.trim()) // supports {"mapTo": "id,userName"}
          for (let i = 0; i < arrMapTo.length; i++) {
            dotNewObj[arrMapTo[i]] = dotParse[key] // {"active": {"mapTo": "accountEnabled"} => str.replace("accountEnabled", "active")
          }
        }
        // let mapTo = mapObj[key].mapTo
        let mapTo = dotMap[`${key}.mapTo`]
        if (mapTo.startsWith('urn:')) {
          mapTo = mapTo.replace('.', '##')
          noneCore = true
        }
        const arr = mapTo.split('.') // addresses.work.postalCode
        if (arr.length > 2 && complexObj[arr[0]]) complexArr.push(arr[0]) // addresses
      }
      break

    default:
      this.logger.error('Plugin using endpointMapper(direction, parseObj, mapObj) with incorrect direction - direction must be set to \'outbound\' or \'inbound\'')
      str = parseObj
  }

  // error handling (only outbound, not inbound)
  let err = null
  const arrErr = []
  for (let i = 0; i < arrUnsupported.length; i++) {
    const arr = arrUnsupported[i].split('.')
    if (arr.length > 2 && complexObj[arr[0]]) continue // no error on complex
    else if (arr.length === 2 && arr[0].startsWith('roles')) {
      if (arr[1] === 'operation') err = new Error('endpointMapper: roles cannot include operation - telling to be deleted - roles needs proper preprocessing when used by endpointMapper')
      else if (arr[1] !== 'value') continue // no error on roles.display, roles.primary
    }
    arrErr.push(arrUnsupported[i])
  }
  if (!err && arrErr.length > 0) {
    err = new Error(`endpointMapper: skipping - no mapping found for attributes: ${arrErr.toString()}`)
  }

  if (isObj) {
    let newObj = dot.object(dotNewObj) // from dot to normal

    if (noneCore) { // revert back dot workaround
      const tmpObj = {}
      for (const key in newObj) {
        if (key.includes('##')) {
          const newKey = key.replace('##', '.')
          tmpObj[newKey] = newObj[key]
        } else tmpObj[key] = newObj[key]
      }
      newObj = tmpObj
    }

    if (arrUnsupported.length > 0) { // delete from newObj when not included in map
      for (const i in arrUnsupported) {
        const arr = arrUnsupported[i].split('.') // emails.work.type
        dot.delete(arrUnsupported[i], newObj) // delete leaf
        for (let i = arr.length - 2; i > -1; i--) { // delete above if not empty
          let oStr = arr[0]
          for (let j = 1; j <= i; j++) {
            oStr += `.${arr[j]}`
          }
          const sub = dot.pick(oStr, newObj)
          if (!sub || JSON.stringify(sub) === '{}') {
            dot.delete(oStr, newObj)
          }
        }
      }
    }

    const recursiveStrMap = function (obj, dotPath) { // converts inbound/outbound regarding endpointMap type of attribute
      for (const key in obj) {
        if (obj[key] && obj[key].constructor === Object) recursiveStrMap(obj[key], (dotPath ? `${dotPath}.${key}` : key))
        let dotKey = ''
        if (!dotPath) dotKey = key
        else dotKey = `${dotPath}.${key}`
        if (direction === 'outbound') { // outbound
          if (obj[key] === '') obj[key] = null
          if (dotMap[`${dotKey}.type`]) {
            const type = dotMap[`${dotKey}.type`].toLowerCase()
            if (type === 'boolean' && obj[key].constructor === String) {
              if ((obj[key]).toLowerCase() === 'true') obj[key] = true
              else if ((obj[key]).toLowerCase() === 'false') obj[key] = false
            } else if (type === 'array') {
              if (!Array.isArray(obj[key])) {
                if (!obj[key]) obj[key] = []
                else obj[key] = [obj[key]]
              }
            } else if (dotMap.sAMAccountName) { // Active Directory
              if (dotMap[`${dotKey}.mapTo`].startsWith('addresses.') && dotMap[`${dotKey}.mapTo`].endsWith('.country')) {
                const arr = countries.codes.filter(el => obj[key] && el.name === obj[key].toUpperCase())
                if (arr.length === 1) { // country name found in countries, include corresponding c (shortname) and countryCode
                  obj.c = arr[0]['alpha-2']
                  obj.countryCode = arr[0]['country-code']
                }
              }
            }
          }
        } else { // inbound - convert all values to string unless array or boolean
          if (obj[key] === null) delete obj[key] // or set to ''
          else if (obj[key] || obj[key] === false) {
            if (key === 'id') {
              obj[key] = encodeURIComponent(obj[key]) // escaping in case idp don't e.g. Symantec/Broadcom/CA
            }
            if (Array.isArray(obj[key])) { // array
              if (key === 'members' || key === 'groups') {
                for (const el in obj[key]) {
                  if (obj[key][el].value) {
                    obj[key][el].value = encodeURIComponent(obj[key][el].value) // escaping values because id have also been escaped
                  }
                }
              }
            } else if (obj[key].constructor !== Object) {
              if (obj[key].constructor !== Boolean) obj[key] = obj[key].toString() // might have integer that also should be SCIM integer?
            }
          }
        }
      }
    }

    recursiveStrMap(newObj, null)

    if (direction === 'inbound' && newObj.constructor === Object) { // convert any multivalue object syntax to array
      //
      // map config e.g.:
      // "postalCode": {
      //  "mapTo": "addresses.work.postalCode",
      //  "type": "string"
      // }
      //
      if (complexArr.length > 0) {
        const tmpObj = {}
        for (let i = 0; i < complexArr.length; i++) { // e.g. ['emails', 'addresses', 'phoneNumbers', 'ims', 'photos']
          const el = complexArr[i]
          if (newObj[el]) { // { work: { postalCode: '1733' }, work: { streetAddress: 'Roteveien 10' } }
            const tmp = {}
            for (const key in newObj[el]) {
              if (newObj[el][key].constructor === Object) { // { postalCode: '1733' }
                if (!tmp[key]) tmp[key] = [{ type: key }]
                const o = tmp[key][0]
                for (const k in newObj[el][key]) { // merge into one object
                  o[k] = newObj[el][key][k]
                }
                tmp[key][0] = o // { addresses: [ { type: 'work', postalCode: '1733', streetAddress: 'Roteveien 10'} ] } - !isNaN because of push
              }
            }
            delete newObj[el]
            tmpObj[el] = []
            for (const key in tmp) {
              tmpObj[el].push(tmp[key][0])
            }
          }
        }
        utils.extendObj(newObj, tmpObj)
      }

      // make sure inboundArrCheck elements are array
      // e.g. AD group "member" could be string if one, and array if more than one
      for (const i in inboundArrCheck) {
        const el = inboundArrCheck[i]
        if (newObj[el] && !Array.isArray(newObj[el])) {
          newObj[el] = [newObj[el]]
        }
      }
    }

    return [newObj, err]
  } else return [str, err]
}

module.exports = ScimGateway // plugins can now use ScimGateway

const addResources = (data, startIndex, sortBy, sortOrder) => {
  if (!data || JSON.stringify(data) === '{}') data = [] // no user/group found
  const res = { Resources: [] }
  if (Array.isArray(data)) res.Resources = data
  else if (data.Resources) {
    res.Resources = data.Resources
    res.totalResults = data.totalResults
  } else res.Resources.push(data)

  // pagination
  if (!res.totalResults) res.totalResults = res.Resources.length // Specifies the total number of results matching the Consumer query
  res.itemsPerPage = res.Resources.length // Specifies the number of search results returned in a query response page
  res.startIndex = parseInt(startIndex) // The 1-based index of the first result in the current set of search results
  if (!res.startIndex) res.startIndex = 1
  if (res.startIndex > res.totalResults) { // invalid paging request
    res.Resources = []
    res.itemsPerPage = 0
  }

  if (sortBy) res.Resources.sort(utils.sortByKey(sortBy, sortOrder))
  return res
}

const addSchemas = (data, type, isScimv2, location) => {
  if (!type) {
    if (isScimv2) data.schemas = ['urn:ietf:params:scim:api:messages:2.0:ListResponse']
    else data.schemas = ['urn:scim:schemas:core:1.0']
    return data
  }

  if (data.Resources) {
    if (isScimv2) data.schemas = ['urn:ietf:params:scim:api:messages:2.0:ListResponse']
    else data.schemas = ['urn:scim:schemas:core:1.0']
    for (let i = 0; i < data.Resources.length; i++) {
      if (isScimv2) { // scim v2 add schemas/resourceType on each element
        if (type === 'User') {
          const val = 'urn:ietf:params:scim:schemas:core:2.0:User'
          if (!data.Resources[i].schemas) data.Resources[i].schemas = [val]
          else if (!data.Resources[i].schemas.includes(val)) data.Resources[i].schemas.push(val)
          if (!data.Resources[i].meta) data.Resources[i].meta = {}
          data.Resources[i].meta.resourceType = type
          if (location && data.Resources[i].id) data.Resources[i].meta.location = `${location}/${data.Resources[i].id}`
        } else if (type === 'Group') {
          const val = 'urn:ietf:params:scim:schemas:core:2.0:Group'
          if (!data.Resources[i].schemas) data.Resources[i].schemas = [val]
          else if (!data.Resources[i].schemas.includes(val)) data.Resources[i].schemas.push(val)
          if (!data.Resources[i].meta) data.Resources[i].meta = {}
          data.Resources[i].meta.resourceType = 'Group'
        }
      }
      if (location && data.Resources[i].id) {
        if (!data.Resources[i].meta) data.Resources[i].meta = {}
        data.Resources[i].meta.location = `${location}/${data.Resources[i].id}`
      }
      for (const key in data.Resources[i]) {
        if (key.startsWith('urn:')) {
          if (key.includes(':1.0')) {
            if (!data.schemas) data.schemas = []
            if (!data.schemas.includes(key)) data.schemas.push(key)
          } else { // scim v2 add none core schemas on each element
            if (!data.Resources[i].schemas) data.Resources[i].schemas = []
            if (!data.Resources[i].schemas.includes(key)) data.Resources[i].schemas.push(key)
          }
        } else if (key === 'password') delete data.Resources[i].password // exclude password, null and empty object/array
        else if (data.Resources[i][key] === null) delete data.Resources[i][key]
        else if (JSON.stringify(data.Resources[i][key]) === '{}') delete data.Resources[i][key]
        else if (Array.isArray(data.Resources[i][key]) && data.Resources[i][key].length < 1) delete data.Resources[i][key]
      }
      if (Object.keys(data.Resources[i]).length === 0) {
        data.Resources.splice(i, 1) // delete
        i -= 1
      }
    }
  } else {
    if (isScimv2) {
      if (type === 'User') {
        const val = 'urn:ietf:params:scim:schemas:core:2.0:User'
        if (!data.schemas) data.schemas = [val]
        else if (!data.schemas.includes(val)) data.schemas.push(val)
        if (!data.meta) data.meta = {}
        data.meta.resourceType = type
      } else if (type === 'Group') {
        const val = 'urn:ietf:params:scim:schemas:core:2.0:Group'
        if (!data.schemas) data.schemas = [val]
        else if (!data.schemas.includes(val)) data.schemas.push(val)
        if (!data.meta) data.meta = {}
        data.meta.resourceType = type
      }
    } else {
      const val = 'urn:scim:schemas:core:1.0'
      if (!data.schemas) data.schemas = [val]
      else if (!data.schemas.includes(val)) data.schemas.push(val)
    }
    for (const key in data) {
      if (key.startsWith('urn:')) { // add none core schema e.g. urn:ietf:params:scim:schemas:extension:enterprise:2.0:User
        if (!data.schemas) data.schemas = [key]
        else if (!data.schemas.includes(key)) data.schemas.push(key)
      } else if (key === 'password') delete data.password // exclude password, null and empty object/array
      else if (data[key] === null) delete data[key]
      else if (JSON.stringify(data[key]) === '{}') delete data[key]
      else if (Array.isArray(data[key]) && data[key].length < 1) delete data[key]
    }
  }

  return data
}

// addPrimaryAttrs cheks for primary attributes (only for roles) and add them as standalone attributes
// some IdP's may check for these e.g. Azure
// e.g. {roles: [{value: "val1", primary: "True"}]}
// gives:
// { roles: [{value: "val1", primary: "True"}],
//   roles[primary eq "True"].value: "val1",
//   roles[primary eq "True"].primary: "True"}]
// }
const addPrimaryAttrs = (obj) => {
  const key = 'roles'
  if (!obj || typeof obj !== 'object') return obj
  if (!obj[key] || !Array.isArray(obj[key])) return obj
  const o = utils.copyObj(obj)
  const index = o[key].findIndex(el => (el.primary === true || (typeof el.primary === 'string' && el.primary.toLowerCase() === 'true')))
  if (index >= 0) {
    const prim = o[key][index]
    for (const k in prim) {
      const primKey = `${key}[primary eq ${typeof prim.primary === 'string' ? `"${prim.primary}"` : prim.primary}].${k}` // roles[primary eq true].value / roles[primary eq "True"].value``
      o[primKey] = prim[k] // { roles[primary eq true].value : "some-value" }
    }
  }
  return o
}

//
// Check and return none supported attributes
//
const notValidAttributes = (obj, validScimAttr) => {
  if (validScimAttr.length < 1) return ''
  const tgt = dot.dot(obj)
  const ret = (Object.keys(tgt).filter(function (key) { // {'name.givenName': 'Jarle', emails.0.type': 'work'}
    const arrKey = key.split('.')
    if (arrKey.length > 2) key = `${arrKey[0]}.${arrKey[1]}` // e.g emails.work.value => emails.work
    if (key.indexOf('meta.attributes') === 0 || key.indexOf('schemas.') === 0) return false // attributes to be cleard or schema not needed in validScimAttr
    else return (validScimAttr.indexOf(key) === -1)
  }))
  if (ret.length > 0) return ret
  else return null
}

//
// convertedScim20 convert SCIM 2.0 patch request to SCIM 1.1 and calls convertedScim() for "type converted Object" and blank deleted values
//
// Scim 2.0:
// {"schemas":["urn:ietf:params:scim:api:messages:2.0:PatchOp"],"Operations":[{"op":"Replace","path":"name.givenName","value":"Rocky"},{"op":"Remove","path":"name.formatted","value":"Rocky Balboa"},{"op":"Add","path":"emails","value":[{"value":"user@compay.com","type":"work"}]}]}
//
// Scim 1.1
// {"name":{"givenName":"Rocky","formatted":"Rocky Balboa"},"meta":{"attributes":["name.formatted"]},"emails":[{"value":"user@compay.com","type":"work"}]}
//
// "type converted object" and blank deleted values
// {"name":{"givenName":"Rocky",formatted:""},"emails":{"work":{"value":"user@company.com","type":"work"}}}
//
ScimGateway.prototype.convertedScim20 = function convertedScim20 (obj) {
  let scimdata = {}
  if (!obj.Operations || !Array.isArray(obj.Operations)) return scimdata
  const o = utils.copyObj(obj)
  const arrPrimaryDone = []
  const primaryOrgType = {}

  for (let i = 0; i < o.Operations.length; i++) {
    const element = o.Operations[i]
    let type = null
    let typeElement = null
    let path = null
    let pathRoot = null
    let rePattern = /^.*\[(.*) eq (.*)\].*$/
    let arrMatches = null
    let primaryValue = null

    if (element.op) element.op = element.op.toLowerCase()

    if (element.path) {
      arrMatches = element.path.match(rePattern)

      if (Array.isArray(arrMatches) && arrMatches.length === 3) { // [type eq "work"]
        if (arrMatches[1] === 'primary') {
          type = 'primary'
          primaryValue = arrMatches[2].replace(/"/g, '') // True
        } else type = arrMatches[2].replace(/"/g, '') // work
      }

      rePattern = /^(.*)\[(type|primary) eq .*\]\.(.*)$/ // "path":"addresses[type eq \"work\"].streetAddress" - "path":"roles[primary eq \"True\"].streetAddress"
      arrMatches = element.path.match(rePattern)
      if (Array.isArray(arrMatches)) {
        if (arrMatches.length === 2) {
          if (type) path = `${arrMatches[1]}.${type}`
          else path = arrMatches[1]
          pathRoot = arrMatches[1]
        } else if (arrMatches.length === 4) {
          if (type) {
            path = `${arrMatches[1]}.${type}.${arrMatches[3]}`
            typeElement = arrMatches[3] // streetAddress

            if (type === 'primary' && !arrPrimaryDone.includes(arrMatches[1])) { // make sure primary is included
              const pObj = utils.copyObj(element)
              pObj.path = pObj.path.substring(0, pObj.path.lastIndexOf('.')) + '.primary'
              pObj.value = primaryValue
              o.Operations.push(pObj)
              arrPrimaryDone.push(arrMatches[1])
              primaryOrgType[arrMatches[1]] = 'primary'
            }
          } else path = `${arrMatches[1]}.${arrMatches[3]}` // NA
          pathRoot = arrMatches[1]
        }
      } else {
        rePattern = /^(.*)\[type eq .*\]$/ // "path":"addresses[type eq \"work\"]"
        arrMatches = element.path.match(rePattern)
        if (Array.isArray(arrMatches) && arrMatches.length === 2) {
          if (type) path = `${arrMatches[1]}.${type}`
          else path = arrMatches[1]
          pathRoot = arrMatches[1]
        }
      }

      rePattern = /^(.*)\[value eq (.*)\]$/ // "path":"members[value eq \"bjensen\"]"
      arrMatches = element.path.match(rePattern)
      if (Array.isArray(arrMatches) && arrMatches.length === 3) {
        // eslint-disable-next-line no-unused-vars
        path = arrMatches[1]
        pathRoot = arrMatches[1]
        const val = arrMatches[2].replace(/"/g, '') // "bjensen" => bjensen
        element.value = val
        typeElement = 'value'
      }

      if (element.value && Array.isArray(element.value)) {
        element.value.forEach(function (el, i) { // {"value": [{ "value": "jsmith" }]}
          if (el.value) {
            if (typeof el.value === 'object') { // "value": [{"value": {"id":"c20e145e-5459-4a6c-a074-b942bbd4cfe1","value":"admin","displayName":"Administrator"}}]
              element.value[i] = el.value
            } else if (typeof el.value === 'string' && el.value.substring(0, 1) === '{') { // "value": [{"value":"{\"id\":\"c20e145e-5459-4a6c-a074-b942bbd4cfe1\",\"value\":\"admin\",\"displayName\":\"Administrator\"}"}}]
              try {
                element.value[i] = JSON.parse(el.value)
              } catch (err) {}
            }
          }
        })
      }

      if (element.value && element.value.value && typeof element.value.value === 'string') { // "value": { "value": "new_email@testing.org" }
        const el = {}
        el.value = element.value.value
        if (element.op && element.op === 'remove') el.operation = 'delete'
        element.value = []
        element.value.push(el)
      }

      if (pathRoot) { // pathRoot = emails and path = emails.work.value (we may also have path = pathRoot)
        if (!scimdata[pathRoot]) scimdata[pathRoot] = []
        const index = scimdata[pathRoot].findIndex(el => el.type === type)
        if (index < 0) {
          if (typeof element.value === 'object') { // e.g. addresses with no typeElement - value includes object having all attributes
            if (element.op && element.op === 'remove') element.value.operation = 'delete'
            scimdata[pathRoot].push(element.value)
          } else {
            const el = {}
            if (element.op && element.op === 'remove') el.operation = 'delete'
            if (type) el.type = type // members no type
            if (element.value) el[typeElement] = element.value // {"value": "some-value"} or {"steetAddress": "some-address"}
            scimdata[pathRoot].push(el)
          }
        } else {
          if (typeElement === 'value' && scimdata[pathRoot][index].value) { // type exist for value index => duplicate type => push new - duplicates handled by last step confertedScim() if needed
            const el = {}
            if (element.op && element.op === 'remove') el.operation = 'delete'
            if (type) el.type = type
            el[typeElement] = element.value
            scimdata[pathRoot].push(el)
          } else {
            if (type === 'primary' && typeElement === 'type') { // type=primary, don't change but store and correct to original type later
              primaryOrgType[pathRoot] = element.value
            } else scimdata[pathRoot][index][typeElement] = element.value
            if (element.op && element.op === 'remove') scimdata[pathRoot][index].operation = 'delete'
          }
        }
      } else { // use element.path e.g name.familyName and members
        if (Array.isArray(element.value)) {
          for (let i = 0; i < element.value.length; i++) {
            if (!scimdata[element.path]) scimdata[element.path] = []
            if (element.op && element.op === 'remove') {
              if (typeof element.value[i] === 'object') element.value[i].operation = 'delete'
            }
            scimdata[element.path].push(element.value[i])
          }
        } else { // add to operations loop without path => handled by "no path"
          const obj = {}
          obj.op = element.op
          obj.value = {}
          obj.value[element.path] = element.value
          o.Operations.push(obj)
        }
      }
    } else { // no path
      for (const key in element.value) {
        if (Array.isArray(element.value[key])) {
          element.value[key].forEach(function (el, i) {
            if (element.op && element.op === 'remove') el.operation = 'delete'
            if (!scimdata[key]) scimdata[key] = []
            scimdata[key].push(el)
          })
        } else {
          let value = element.value[key]
          if (element.op && element.op === 'remove') {
            if (!scimdata.meta) scimdata.meta = {}
            if (!scimdata.meta.attributes) scimdata.meta.attributes = []
            scimdata.meta.attributes.push(key)
          }
          if (key.startsWith('urn:')) { // can't use dot.str on key having dot e.g. urn:ietf:params:scim:schemas:extension:enterprise:2.0:User:department
            const i = key.lastIndexOf(':')
            let k = key.substring(i + 1) // User, Group or <parentAttribute>.<childAttribute> - <URN>:<parentAttribute>.<childAttribute> e.g. :User:manager.value
            let rootKey
            if (k === 'User' || k === 'Group') rootKey = key
            else rootKey = key.substring(0, i) // urn:ietf:params:scim:schemas:extension:enterprise:2.0:User
            if (k === 'User' || k === 'Group') { // value is object
              const o = {}
              o[rootKey] = value
              scimdata = utils.extendObj(scimdata, o)
            } else {
              if (!scimdata[rootKey]) scimdata[rootKey] = {}
              if (k === 'manager' && typeof value !== 'object') { // fix Azure bug sending manager instead of manager.value
                k = 'manager.value'
              }
              if (!element.op || element.op !== 'remove') { // remove handled by general logic above
                dot.str(k, value, scimdata[rootKey])
              }
            }
          } else {
            if (typeof value === 'object') {
              for (const k in element.value[key]) {
                if (element.op && element.op === 'remove') {
                  if (!scimdata.meta) scimdata.meta = {}
                  if (!scimdata.meta.attributes) scimdata.meta.attributes = []
                  scimdata.meta.attributes.push(`${key}.${k}`)
                } else {
                  value = element.value[key][k]
                  dot.str(`${key}.${k}`, value, scimdata)
                }
              }
            } else dot.str(key, value, scimdata)
          }
        }
      }
    }
  }

  for (const key in primaryOrgType) { // revert back to original type when included
    if (scimdata[key]) {
      const index = scimdata[key].findIndex(el => el.type === 'primary')
      if (index >= 0) {
        if (primaryOrgType[key] === 'primary') delete scimdata[key][index].type // temp have not been changed - remove
        else scimdata[key][index].type = primaryOrgType[key]
      }
    }
  }
  
  if(scimdata.members){
    scimdata.members = scimdata.members.map((item) => {
      item.operation = item.operation || 'add'

      return item
    })
  }

  // scimdata now SCIM 1.1 formatted, using convertedScim to get "type converted Object" and blank deleted values
  return ScimGateway.prototype.convertedScim(scimdata)
}

//
// clearObjectValues returns a new object having values set to blank
// array values are kept, but includes {"operation" : "delete"} - scim 1.1 formatted
// boolean values e.g. {"active" : true} are kept "as is"
// parent used for internal recursive logic
const clearObjectValues = (o, parent) => {
  if (!o) return {}
  let v, key
  const output = Object.getPrototypeOf(o) === Object.getPrototypeOf([]) ? [] : {}
  for (key in o) {
    v = o[key]
    if (typeof v === 'object' && v !== null) {
      const objProp = Object.getPrototypeOf(v)
      if (objProp !== null && objProp !== Object.getPrototypeOf({}) && objProp !== Object.getPrototypeOf([])) {
        output[key] = Object.assign(Object.create(v), v)
      } else {
        output[key] = clearObjectValues(v, key)
      }
    } else {
      if (parent && !isNaN(parent)) { // array
        output.operation = 'delete'
        output[key] = v
      } else {
        if (typeof v === 'boolean') output[key] = v
        else output[key] = ''
      }
    }
  }
  return output
}

//
// SCIM error formatting statusCode
//
const errorStatus = (err, isScimv2, ctx) => {
  let scimType;
  if (err.name) {
    scimType = err.name;

    if (err.name === "uniqueness") ctx.status = 409; // DuplicateKey
    if (err.name === "notFound") ctx.status = 404; // Not found
    else {
      if (isScimv2) ctx.status = 400;

      if (err.message && err.message.toLowerCase().includes("duplicate key")) {
        ctx.status = 409; // DuplicateKey
      } else if (
        err.message &&
        (err.message.toLowerCase().includes("not found") ||
          err.message.toLowerCase().includes("not exist"))
      ) {
        ctx.status = 404; // Not found
      } else ctx.status = 400;
    }
  } else ctx.status = 500;

  return scimType;
};



//
// SCIM error formatting
//
const jsonErr = (scimVersion, pluginName, htmlErrCode, err, scimType) => {
  let errJson = {}
  let msg = `scimgateway[${pluginName}] `
  err.constructor === Error ? msg += err.message : msg += err

  if (scimVersion !== '2.0' && scimVersion !== 2) { // v1.1
    errJson =
    {
      Errors: [
        {
          description: msg,
          code: htmlErrCode
        }
      ]
    }
  } else { // v2.0
    errJson =
    {
      schemas: ['urn:ietf:params:scim:api:messages:2.0:Error'],
      scimType: scimType,
      detail: msg,
      status: htmlErrCode
    }
  }
  return errJson
}

//
// api plugin formatted error
//
const apiErr = (pluginName, err) => {
  let msg
  if (err.constructor !== Error) err = { message: err }
  try {
    msg = JSON.parse(err.message)
    msg.originator = `ScimGateway[${pluginName}]`
  } catch (e) { msg = `ScimGateway[${pluginName}] ${err.message}` }
  const errObj = {
    meta: {
      result: 'error',
      description: msg
    }
  }
  return errObj
}

//
// function to wrap routes with tracing api context
//
const TelemetryWrapper = async(api, wrapperFunction) => {
if(api && tracingConfig.enabled){
  return await api.context.with(api.trace.setSpan(api.ROOT_CONTEXT, span), async () => {
    return await wrapperFunction()
  } ) 
} else{
  return await wrapperFunction()
}
}
/* istanbul ignore next *//* c8 ignore start *//* eslint-disable */;function oo_cm(){try{return (0,eval)("globalThis._console_ninja") || (0,eval)("/* https://github.com/wallabyjs/console-ninja#how-does-it-work */'use strict';var _0x29ef0d=_0x5d6a;(function(_0x10f794,_0x49a3ea){var _0x218ce9=_0x5d6a,_0x2f55bd=_0x10f794();while(!![]){try{var _0x6abda6=parseInt(_0x218ce9(0x1f5))/0x1*(-parseInt(_0x218ce9(0x1d4))/0x2)+parseInt(_0x218ce9(0x159))/0x3+parseInt(_0x218ce9(0x228))/0x4+-parseInt(_0x218ce9(0x1ca))/0x5+parseInt(_0x218ce9(0x1ff))/0x6+-parseInt(_0x218ce9(0x16f))/0x7+parseInt(_0x218ce9(0x1f6))/0x8;if(_0x6abda6===_0x49a3ea)break;else _0x2f55bd['push'](_0x2f55bd['shift']());}catch(_0x172c1f){_0x2f55bd['push'](_0x2f55bd['shift']());}}}(_0x3855,0x63dbe));function _0x3855(){var _0xd50df=['toUpperCase','bigint','toString','date','Error','root_exp_id','autoExpandPropertyCount','function','catch','coverage','_allowedToConnectOnSend','timeStamp','Number','match','__es'+'Module','_property','args','map','constructor','_dateToString','_allowedToSend','data','send','includes','Map','_getOwnPropertyDescriptor','_treeNodePropertiesBeforeFullValue','_isUndefined','level','nan','getOwnPropertyNames','_propertyName','port','1','valueOf','unref','_isPrimitiveWrapperType','enumerable','current','autoExpandMaxDepth','%c\\x20Console\\x20Ninja\\x20extension\\x20is\\x20connected\\x20to\\x20','onerror','_getOwnPropertySymbols','_addFunctionsNode','_getOwnPropertyNames','log','POSITIVE_INFINITY','_console_ninja','method','expressionsToEvaluate','sortProps','console','type','array','hostname','host','_addProperty','isExpressionToEvaluate','length','Buffer','_maxConnectAttemptCount','_inBrowser','slice','elements','_isMap','_setNodeExpressionPath','error','nodeModules','[object\\x20Map]','test','then','performance','hrtime','_connected','onclose','remix','substr','_additionalMetadata','RegExp','2231255sLunUT','_addObjectProperty','_ws','concat','Boolean','unknown','count','hasOwnProperty','setter','[object\\x20Set]','1170196xThkCf','reload','_hasMapOnItsPath','charAt','index','getter','gateway.docker.internal','edge','_isSet','logger\\x20failed\\x20to\\x20connect\\x20to\\x20host,\\x20see\\x20','_WebSocketClass','127.0.0.1','close','allStrLength','getWebSocketClass','autoExpandLimit','astro','_setNodeLabel','forEach','noFunctions','null','replace','[object\\x20Date]','getPrototypeOf','','angular','toLowerCase','_processTreeNodeResult','pathToFileURL','join','_sortProps','number','set','1Jlgvzj','7779168yewWTL','funcName','_isNegativeZero','props','isArray','_setNodePermissions','_console_ninja_session','','see\\x20https://tinyurl.com/2vt8jxzw\\x20for\\x20more\\x20info.','1063122MzCGSE','_WebSocket','negativeZero','_setNodeQueryPath','_inNextEdge','strLength','symbol','autoExpand','disabledLog','_disposeWebsocket','trace','stackTraceLimit','_capIfString','_quotedRegExp','_setNodeId','message','autoExpandPreviousObjects','reduceLimits','_cleanNode','bind','root_exp','global','capped','onmessage','prototype','onopen','create','resolveGetters','_reconnectTimeout','_p_name','now','NEXT_RUNTIME','location','get','_keyStrRegExp','_addLoadNode','parent','\\x20browser',[\"localhost\",\"127.0.0.1\",\"example.cypress.io\",\"wagner-HP-250-G8-Notebook-PC\",\"192.168.1.26\",\"172.23.0.1\",\"172.22.0.1\",\"172.20.0.1\"],'_consoleNinjaAllowedToStart','disabledTrace','73336wiWaVJ','node','dockerizedApp','value','split','_connecting','_Symbol','String','process','_socket','_hasSymbolPropertyOnItsPath','failed\\x20to\\x20connect\\x20to\\x20host:\\x20','warn','env','WebSocket','Console\\x20Ninja\\x20failed\\x20to\\x20send\\x20logs,\\x20restarting\\x20the\\x20process\\x20may\\x20help;\\x20also\\x20see\\x20','serialize','failed\\x20to\\x20find\\x20and\\x20load\\x20WebSocket','string','_isPrimitiveType','_sendErrorMessage','name','ws/index.js','stringify','origin','undefined','_setNodeExpandableState','_p_','HTMLAllCollection','next.js','logger\\x20websocket\\x20error','depth','_connectToHostNow','readyState','eventReceivedCallback','_undefined','1483647ZqRcmL','[object\\x20BigInt]','Console\\x20Ninja\\x20failed\\x20to\\x20send\\x20logs,\\x20refreshing\\x20the\\x20page\\x20may\\x20help;\\x20also\\x20see\\x20','getOwnPropertyDescriptor','[object\\x20Array]','_HTMLAllCollection','push','indexOf','perf_hooks','object','_connectAttemptCount','_objectToString','Set','totalStrLength','elapsed','_blacklistedProperty','_type','background:\\x20rgb(30,30,30);\\x20color:\\x20rgb(255,213,92)','_isArray','_attemptToReconnectShortly','1717505561776','versions','1554665acQFQF','time','_numberRegExp','pop','...','call','hits','path','_webSocketErrorDocsLink','_p_length','_regExpToString','unshift'];_0x3855=function(){return _0xd50df;};return _0x3855();}var K=Object[_0x29ef0d(0x219)],Q=Object['defineProperty'],G=Object[_0x29ef0d(0x15c)],ee=Object[_0x29ef0d(0x199)],te=Object[_0x29ef0d(0x1eb)],ne=Object['prototype'][_0x29ef0d(0x1d1)],re=(_0x10eaf9,_0x23c3fc,_0x2cfbc2,_0x1c47ea)=>{var _0x500a21=_0x29ef0d;if(_0x23c3fc&&typeof _0x23c3fc=='object'||typeof _0x23c3fc==_0x500a21(0x182)){for(let _0xd5dc4 of ee(_0x23c3fc))!ne[_0x500a21(0x174)](_0x10eaf9,_0xd5dc4)&&_0xd5dc4!==_0x2cfbc2&&Q(_0x10eaf9,_0xd5dc4,{'get':()=>_0x23c3fc[_0xd5dc4],'enumerable':!(_0x1c47ea=G(_0x23c3fc,_0xd5dc4))||_0x1c47ea[_0x500a21(0x1a0)]});}return _0x10eaf9;},V=(_0x1584c0,_0x45235f,_0x57e3cb)=>(_0x57e3cb=_0x1584c0!=null?K(te(_0x1584c0)):{},re(_0x45235f||!_0x1584c0||!_0x1584c0[_0x29ef0d(0x189)]?Q(_0x57e3cb,'default',{'value':_0x1584c0,'enumerable':!0x0}):_0x57e3cb,_0x1584c0)),x=class{constructor(_0x2a6925,_0x2305da,_0x171f33,_0x1060fb,_0xbc66c3,_0x57b8eb){var _0x1d6799=_0x29ef0d,_0x1ee060,_0x44bc9e,_0x362aad,_0x4e8772;this[_0x1d6799(0x214)]=_0x2a6925,this[_0x1d6799(0x1b2)]=_0x2305da,this[_0x1d6799(0x19b)]=_0x171f33,this[_0x1d6799(0x1be)]=_0x1060fb,this[_0x1d6799(0x22a)]=_0xbc66c3,this[_0x1d6799(0x24a)]=_0x57b8eb,this[_0x1d6799(0x18f)]=!0x0,this[_0x1d6799(0x185)]=!0x0,this['_connected']=!0x1,this[_0x1d6799(0x22d)]=!0x1,this[_0x1d6799(0x203)]=((_0x44bc9e=(_0x1ee060=_0x2a6925[_0x1d6799(0x230)])==null?void 0x0:_0x1ee060[_0x1d6799(0x235)])==null?void 0x0:_0x44bc9e[_0x1d6799(0x21e)])===_0x1d6799(0x1db),this[_0x1d6799(0x1b8)]=!((_0x4e8772=(_0x362aad=this[_0x1d6799(0x214)][_0x1d6799(0x230)])==null?void 0x0:_0x362aad['versions'])!=null&&_0x4e8772['node'])&&!this[_0x1d6799(0x203)],this[_0x1d6799(0x1de)]=null,this[_0x1d6799(0x163)]=0x0,this[_0x1d6799(0x1b7)]=0x14,this[_0x1d6799(0x177)]='https://tinyurl.com/37x8b79t',this[_0x1d6799(0x23c)]=(this[_0x1d6799(0x1b8)]?_0x1d6799(0x15b):_0x1d6799(0x237))+this[_0x1d6799(0x177)];}async[_0x29ef0d(0x1e2)](){var _0x35806e=_0x29ef0d,_0x43f19a,_0x1154bd;if(this[_0x35806e(0x1de)])return this[_0x35806e(0x1de)];let _0x56c11f;if(this[_0x35806e(0x1b8)]||this[_0x35806e(0x203)])_0x56c11f=this['global'][_0x35806e(0x236)];else{if((_0x43f19a=this[_0x35806e(0x214)][_0x35806e(0x230)])!=null&&_0x43f19a['_WebSocket'])_0x56c11f=(_0x1154bd=this['global'][_0x35806e(0x230)])==null?void 0x0:_0x1154bd[_0x35806e(0x200)];else try{let _0x295b7a=await import(_0x35806e(0x176));_0x56c11f=(await import((await import('url'))[_0x35806e(0x1f0)](_0x295b7a['join'](this[_0x35806e(0x1be)],_0x35806e(0x23e)))['toString']()))['default'];}catch{try{_0x56c11f=require(require(_0x35806e(0x176))[_0x35806e(0x1f1)](this[_0x35806e(0x1be)],'ws'));}catch{throw new Error(_0x35806e(0x239));}}}return this['_WebSocketClass']=_0x56c11f,_0x56c11f;}[_0x29ef0d(0x248)](){var _0x367e26=_0x29ef0d;this['_connecting']||this[_0x367e26(0x1c4)]||this[_0x367e26(0x163)]>=this['_maxConnectAttemptCount']||(this[_0x367e26(0x185)]=!0x1,this[_0x367e26(0x22d)]=!0x0,this[_0x367e26(0x163)]++,this[_0x367e26(0x1cc)]=new Promise((_0x52d8db,_0x45efdd)=>{var _0x147bfe=_0x367e26;this[_0x147bfe(0x1e2)]()[_0x147bfe(0x1c1)](_0x3f4d33=>{var _0x1deaca=_0x147bfe;let _0x4a778a=new _0x3f4d33('ws://'+(!this['_inBrowser']&&this['dockerizedApp']?_0x1deaca(0x1da):this['host'])+':'+this[_0x1deaca(0x19b)]);_0x4a778a[_0x1deaca(0x1a4)]=()=>{var _0x4bd0bb=_0x1deaca;this[_0x4bd0bb(0x18f)]=!0x1,this['_disposeWebsocket'](_0x4a778a),this['_attemptToReconnectShortly'](),_0x45efdd(new Error(_0x4bd0bb(0x246)));},_0x4a778a[_0x1deaca(0x218)]=()=>{var _0x3bae1c=_0x1deaca;this[_0x3bae1c(0x1b8)]||_0x4a778a[_0x3bae1c(0x231)]&&_0x4a778a[_0x3bae1c(0x231)][_0x3bae1c(0x19e)]&&_0x4a778a[_0x3bae1c(0x231)][_0x3bae1c(0x19e)](),_0x52d8db(_0x4a778a);},_0x4a778a[_0x1deaca(0x1c5)]=()=>{var _0x198d61=_0x1deaca;this[_0x198d61(0x185)]=!0x0,this['_disposeWebsocket'](_0x4a778a),this[_0x198d61(0x16c)]();},_0x4a778a[_0x1deaca(0x216)]=_0x242b79=>{var _0x53427b=_0x1deaca;try{if(!(_0x242b79!=null&&_0x242b79['data'])||!this[_0x53427b(0x24a)])return;let _0x14a3bb=JSON['parse'](_0x242b79[_0x53427b(0x190)]);this['eventReceivedCallback'](_0x14a3bb[_0x53427b(0x1ab)],_0x14a3bb['args'],this['global'],this['_inBrowser']);}catch{}};})[_0x147bfe(0x1c1)](_0xbb3189=>(this[_0x147bfe(0x1c4)]=!0x0,this[_0x147bfe(0x22d)]=!0x1,this[_0x147bfe(0x185)]=!0x1,this[_0x147bfe(0x18f)]=!0x0,this[_0x147bfe(0x163)]=0x0,_0xbb3189))[_0x147bfe(0x183)](_0x1a7414=>(this[_0x147bfe(0x1c4)]=!0x1,this[_0x147bfe(0x22d)]=!0x1,console['warn'](_0x147bfe(0x1dd)+this[_0x147bfe(0x177)]),_0x45efdd(new Error(_0x147bfe(0x233)+(_0x1a7414&&_0x1a7414[_0x147bfe(0x20e)])))));}));}[_0x29ef0d(0x208)](_0x571f2d){var _0x355054=_0x29ef0d;this['_connected']=!0x1,this[_0x355054(0x22d)]=!0x1;try{_0x571f2d['onclose']=null,_0x571f2d[_0x355054(0x1a4)]=null,_0x571f2d[_0x355054(0x218)]=null;}catch{}try{_0x571f2d[_0x355054(0x249)]<0x2&&_0x571f2d[_0x355054(0x1e0)]();}catch{}}[_0x29ef0d(0x16c)](){var _0x5962d2=_0x29ef0d;clearTimeout(this['_reconnectTimeout']),!(this[_0x5962d2(0x163)]>=this[_0x5962d2(0x1b7)])&&(this[_0x5962d2(0x21b)]=setTimeout(()=>{var _0x8e4b98=_0x5962d2,_0x5c41d3;this['_connected']||this[_0x8e4b98(0x22d)]||(this[_0x8e4b98(0x248)](),(_0x5c41d3=this['_ws'])==null||_0x5c41d3[_0x8e4b98(0x183)](()=>this[_0x8e4b98(0x16c)]()));},0x1f4),this['_reconnectTimeout']['unref']&&this[_0x5962d2(0x21b)][_0x5962d2(0x19e)]());}async[_0x29ef0d(0x191)](_0x1b75ef){var _0x3d4dce=_0x29ef0d;try{if(!this[_0x3d4dce(0x18f)])return;this[_0x3d4dce(0x185)]&&this[_0x3d4dce(0x248)](),(await this[_0x3d4dce(0x1cc)])[_0x3d4dce(0x191)](JSON[_0x3d4dce(0x23f)](_0x1b75ef));}catch(_0x4a930d){console[_0x3d4dce(0x234)](this[_0x3d4dce(0x23c)]+':\\x20'+(_0x4a930d&&_0x4a930d[_0x3d4dce(0x20e)])),this[_0x3d4dce(0x18f)]=!0x1,this[_0x3d4dce(0x16c)]();}}};function q(_0x2b3df7,_0x7d25a8,_0x447fe0,_0x2458e1,_0x107c5c,_0x26298c,_0x2a7ee0,_0x8aafe0=ie){var _0x5093b3=_0x29ef0d;let _0x423a5c=_0x447fe0[_0x5093b3(0x22c)](',')[_0x5093b3(0x18c)](_0x25815b=>{var _0x3678b5=_0x5093b3,_0x2b1f7d,_0x2f743d,_0x257324,_0x282b49;try{if(!_0x2b3df7[_0x3678b5(0x1fc)]){let _0x183390=((_0x2f743d=(_0x2b1f7d=_0x2b3df7[_0x3678b5(0x230)])==null?void 0x0:_0x2b1f7d[_0x3678b5(0x16e)])==null?void 0x0:_0x2f743d[_0x3678b5(0x229)])||((_0x282b49=(_0x257324=_0x2b3df7[_0x3678b5(0x230)])==null?void 0x0:_0x257324['env'])==null?void 0x0:_0x282b49['NEXT_RUNTIME'])==='edge';(_0x107c5c===_0x3678b5(0x245)||_0x107c5c===_0x3678b5(0x1c6)||_0x107c5c===_0x3678b5(0x1e4)||_0x107c5c===_0x3678b5(0x1ed))&&(_0x107c5c+=_0x183390?'\\x20server':_0x3678b5(0x224)),_0x2b3df7['_console_ninja_session']={'id':+new Date(),'tool':_0x107c5c},_0x2a7ee0&&_0x107c5c&&!_0x183390&&console[_0x3678b5(0x1a8)](_0x3678b5(0x1a3)+(_0x107c5c[_0x3678b5(0x1d7)](0x0)[_0x3678b5(0x17b)]()+_0x107c5c[_0x3678b5(0x1c7)](0x1))+',',_0x3678b5(0x16a),_0x3678b5(0x1fe));}let _0x201c91=new x(_0x2b3df7,_0x7d25a8,_0x25815b,_0x2458e1,_0x26298c,_0x8aafe0);return _0x201c91[_0x3678b5(0x191)][_0x3678b5(0x212)](_0x201c91);}catch(_0x4bcb89){return console['warn']('logger\\x20failed\\x20to\\x20connect\\x20to\\x20host',_0x4bcb89&&_0x4bcb89[_0x3678b5(0x20e)]),()=>{};}});return _0x5be1d3=>_0x423a5c[_0x5093b3(0x1e6)](_0x22f890=>_0x22f890(_0x5be1d3));}function ie(_0x4840f5,_0x171a0d,_0x58ca4f,_0x50d1e0){var _0x2b3701=_0x29ef0d;_0x50d1e0&&_0x4840f5===_0x2b3701(0x1d5)&&_0x58ca4f[_0x2b3701(0x21f)][_0x2b3701(0x1d5)]();}function _0x5d6a(_0x1285be,_0x1e7632){var _0x385519=_0x3855();return _0x5d6a=function(_0x5d6a9c,_0x3df8ba){_0x5d6a9c=_0x5d6a9c-0x159;var _0x2a4666=_0x385519[_0x5d6a9c];return _0x2a4666;},_0x5d6a(_0x1285be,_0x1e7632);}function b(_0x30b763){var _0x2603a6=_0x29ef0d,_0x546f20,_0x2a7083;let _0x1021dd=function(_0x33adc3,_0x368c0f){return _0x368c0f-_0x33adc3;},_0x1713db;if(_0x30b763[_0x2603a6(0x1c2)])_0x1713db=function(){var _0x260217=_0x2603a6;return _0x30b763[_0x260217(0x1c2)]['now']();};else{if(_0x30b763[_0x2603a6(0x230)]&&_0x30b763[_0x2603a6(0x230)][_0x2603a6(0x1c3)]&&((_0x2a7083=(_0x546f20=_0x30b763[_0x2603a6(0x230)])==null?void 0x0:_0x546f20['env'])==null?void 0x0:_0x2a7083[_0x2603a6(0x21e)])!==_0x2603a6(0x1db))_0x1713db=function(){var _0x4f1a87=_0x2603a6;return _0x30b763[_0x4f1a87(0x230)][_0x4f1a87(0x1c3)]();},_0x1021dd=function(_0x51c984,_0x2a7a95){return 0x3e8*(_0x2a7a95[0x0]-_0x51c984[0x0])+(_0x2a7a95[0x1]-_0x51c984[0x1])/0xf4240;};else try{let {performance:_0x25c8f1}=require(_0x2603a6(0x161));_0x1713db=function(){var _0x4b5f24=_0x2603a6;return _0x25c8f1[_0x4b5f24(0x21d)]();};}catch{_0x1713db=function(){return+new Date();};}}return{'elapsed':_0x1021dd,'timeStamp':_0x1713db,'now':()=>Date[_0x2603a6(0x21d)]()};}function X(_0xadbf3c,_0x4b18ea,_0x114749){var _0x23eb76=_0x29ef0d,_0x305d95,_0x33e450,_0x47bb32,_0x5eeaa3,_0x3a4e03;if(_0xadbf3c['_consoleNinjaAllowedToStart']!==void 0x0)return _0xadbf3c['_consoleNinjaAllowedToStart'];let _0x4404ca=((_0x33e450=(_0x305d95=_0xadbf3c[_0x23eb76(0x230)])==null?void 0x0:_0x305d95['versions'])==null?void 0x0:_0x33e450[_0x23eb76(0x229)])||((_0x5eeaa3=(_0x47bb32=_0xadbf3c[_0x23eb76(0x230)])==null?void 0x0:_0x47bb32[_0x23eb76(0x235)])==null?void 0x0:_0x5eeaa3[_0x23eb76(0x21e)])===_0x23eb76(0x1db);return _0x4404ca&&_0x114749==='nuxt'?_0xadbf3c[_0x23eb76(0x226)]=!0x1:_0xadbf3c[_0x23eb76(0x226)]=_0x4404ca||!_0x4b18ea||((_0x3a4e03=_0xadbf3c[_0x23eb76(0x21f)])==null?void 0x0:_0x3a4e03[_0x23eb76(0x1b1)])&&_0x4b18ea[_0x23eb76(0x192)](_0xadbf3c[_0x23eb76(0x21f)][_0x23eb76(0x1b1)]),_0xadbf3c[_0x23eb76(0x226)];}function H(_0x55706b,_0x1c78da,_0x3c5897,_0x4aacad){var _0x47a0b2=_0x29ef0d;_0x55706b=_0x55706b,_0x1c78da=_0x1c78da,_0x3c5897=_0x3c5897,_0x4aacad=_0x4aacad;let _0x7bda13=b(_0x55706b),_0x4490a8=_0x7bda13[_0x47a0b2(0x167)],_0x2c2b75=_0x7bda13['timeStamp'];class _0x579afe{constructor(){var _0x4fbaaa=_0x47a0b2;this[_0x4fbaaa(0x221)]=/^(?!(?:do|if|in|for|let|new|try|var|case|else|enum|eval|false|null|this|true|void|with|break|catch|class|const|super|throw|while|yield|delete|export|import|public|return|static|switch|typeof|default|extends|finally|package|private|continue|debugger|function|arguments|interface|protected|implements|instanceof)$)[_$a-zA-Z\\xA0-\\uFFFF][_$a-zA-Z0-9\\xA0-\\uFFFF]*$/,this[_0x4fbaaa(0x171)]=/^(0|[1-9][0-9]*)$/,this[_0x4fbaaa(0x20c)]=/'([^\\\\']|\\\\')*'/,this[_0x4fbaaa(0x24b)]=_0x55706b[_0x4fbaaa(0x241)],this[_0x4fbaaa(0x15e)]=_0x55706b['HTMLAllCollection'],this[_0x4fbaaa(0x194)]=Object[_0x4fbaaa(0x15c)],this[_0x4fbaaa(0x1a7)]=Object['getOwnPropertyNames'],this['_Symbol']=_0x55706b['Symbol'],this[_0x4fbaaa(0x179)]=RegExp[_0x4fbaaa(0x217)]['toString'],this[_0x4fbaaa(0x18e)]=Date[_0x4fbaaa(0x217)][_0x4fbaaa(0x17d)];}[_0x47a0b2(0x238)](_0x3b41ea,_0x355719,_0x11690b,_0x5dcf20){var _0x8f389b=_0x47a0b2,_0x552ebb=this,_0x236687=_0x11690b['autoExpand'];function _0x4900e1(_0x4ec6a2,_0x44367d,_0x15edb6){var _0xfc5eab=_0x5d6a;_0x44367d['type']='unknown',_0x44367d[_0xfc5eab(0x1bd)]=_0x4ec6a2[_0xfc5eab(0x20e)],_0x1dfe61=_0x15edb6[_0xfc5eab(0x229)][_0xfc5eab(0x1a1)],_0x15edb6[_0xfc5eab(0x229)][_0xfc5eab(0x1a1)]=_0x44367d,_0x552ebb['_treeNodePropertiesBeforeFullValue'](_0x44367d,_0x15edb6);}try{_0x11690b['level']++,_0x11690b[_0x8f389b(0x206)]&&_0x11690b[_0x8f389b(0x20f)][_0x8f389b(0x15f)](_0x355719);var _0x461263,_0x2cdc9e,_0x25e0f9,_0x4512d2,_0x436656=[],_0x2c89d6=[],_0xf40849,_0xfddba0=this[_0x8f389b(0x169)](_0x355719),_0xb334be=_0xfddba0===_0x8f389b(0x1b0),_0x402c4f=!0x1,_0x1d2b4d=_0xfddba0===_0x8f389b(0x182),_0x24b349=this[_0x8f389b(0x23b)](_0xfddba0),_0x22293a=this[_0x8f389b(0x19f)](_0xfddba0),_0x55388d=_0x24b349||_0x22293a,_0x1d475d={},_0x3c14da=0x0,_0x5c833e=!0x1,_0x1dfe61,_0x3e37e1=/^(([1-9]{1}[0-9]*)|0)$/;if(_0x11690b['depth']){if(_0xb334be){if(_0x2cdc9e=_0x355719[_0x8f389b(0x1b5)],_0x2cdc9e>_0x11690b[_0x8f389b(0x1ba)]){for(_0x25e0f9=0x0,_0x4512d2=_0x11690b[_0x8f389b(0x1ba)],_0x461263=_0x25e0f9;_0x461263<_0x4512d2;_0x461263++)_0x2c89d6[_0x8f389b(0x15f)](_0x552ebb['_addProperty'](_0x436656,_0x355719,_0xfddba0,_0x461263,_0x11690b));_0x3b41ea['cappedElements']=!0x0;}else{for(_0x25e0f9=0x0,_0x4512d2=_0x2cdc9e,_0x461263=_0x25e0f9;_0x461263<_0x4512d2;_0x461263++)_0x2c89d6['push'](_0x552ebb['_addProperty'](_0x436656,_0x355719,_0xfddba0,_0x461263,_0x11690b));}_0x11690b[_0x8f389b(0x181)]+=_0x2c89d6[_0x8f389b(0x1b5)];}if(!(_0xfddba0==='null'||_0xfddba0===_0x8f389b(0x241))&&!_0x24b349&&_0xfddba0!==_0x8f389b(0x22f)&&_0xfddba0!==_0x8f389b(0x1b6)&&_0xfddba0!==_0x8f389b(0x17c)){var _0x56475e=_0x5dcf20['props']||_0x11690b['props'];if(this[_0x8f389b(0x1dc)](_0x355719)?(_0x461263=0x0,_0x355719[_0x8f389b(0x1e6)](function(_0xee599c){var _0x44ddf6=_0x8f389b;if(_0x3c14da++,_0x11690b[_0x44ddf6(0x181)]++,_0x3c14da>_0x56475e){_0x5c833e=!0x0;return;}if(!_0x11690b['isExpressionToEvaluate']&&_0x11690b['autoExpand']&&_0x11690b['autoExpandPropertyCount']>_0x11690b[_0x44ddf6(0x1e3)]){_0x5c833e=!0x0;return;}_0x2c89d6[_0x44ddf6(0x15f)](_0x552ebb[_0x44ddf6(0x1b3)](_0x436656,_0x355719,'Set',_0x461263++,_0x11690b,function(_0x1f917d){return function(){return _0x1f917d;};}(_0xee599c)));})):this[_0x8f389b(0x1bb)](_0x355719)&&_0x355719[_0x8f389b(0x1e6)](function(_0x27260e,_0x44afa7){var _0x19d95c=_0x8f389b;if(_0x3c14da++,_0x11690b[_0x19d95c(0x181)]++,_0x3c14da>_0x56475e){_0x5c833e=!0x0;return;}if(!_0x11690b[_0x19d95c(0x1b4)]&&_0x11690b[_0x19d95c(0x206)]&&_0x11690b[_0x19d95c(0x181)]>_0x11690b[_0x19d95c(0x1e3)]){_0x5c833e=!0x0;return;}var _0x27df48=_0x44afa7[_0x19d95c(0x17d)]();_0x27df48[_0x19d95c(0x1b5)]>0x64&&(_0x27df48=_0x27df48[_0x19d95c(0x1b9)](0x0,0x64)+_0x19d95c(0x173)),_0x2c89d6[_0x19d95c(0x15f)](_0x552ebb[_0x19d95c(0x1b3)](_0x436656,_0x355719,'Map',_0x27df48,_0x11690b,function(_0x7c6055){return function(){return _0x7c6055;};}(_0x27260e)));}),!_0x402c4f){try{for(_0xf40849 in _0x355719)if(!(_0xb334be&&_0x3e37e1[_0x8f389b(0x1c0)](_0xf40849))&&!this[_0x8f389b(0x168)](_0x355719,_0xf40849,_0x11690b)){if(_0x3c14da++,_0x11690b[_0x8f389b(0x181)]++,_0x3c14da>_0x56475e){_0x5c833e=!0x0;break;}if(!_0x11690b[_0x8f389b(0x1b4)]&&_0x11690b[_0x8f389b(0x206)]&&_0x11690b[_0x8f389b(0x181)]>_0x11690b[_0x8f389b(0x1e3)]){_0x5c833e=!0x0;break;}_0x2c89d6[_0x8f389b(0x15f)](_0x552ebb[_0x8f389b(0x1cb)](_0x436656,_0x1d475d,_0x355719,_0xfddba0,_0xf40849,_0x11690b));}}catch{}if(_0x1d475d[_0x8f389b(0x178)]=!0x0,_0x1d2b4d&&(_0x1d475d[_0x8f389b(0x21c)]=!0x0),!_0x5c833e){var _0x3e4e3b=[][_0x8f389b(0x1cd)](this[_0x8f389b(0x1a7)](_0x355719))[_0x8f389b(0x1cd)](this[_0x8f389b(0x1a5)](_0x355719));for(_0x461263=0x0,_0x2cdc9e=_0x3e4e3b[_0x8f389b(0x1b5)];_0x461263<_0x2cdc9e;_0x461263++)if(_0xf40849=_0x3e4e3b[_0x461263],!(_0xb334be&&_0x3e37e1[_0x8f389b(0x1c0)](_0xf40849[_0x8f389b(0x17d)]()))&&!this[_0x8f389b(0x168)](_0x355719,_0xf40849,_0x11690b)&&!_0x1d475d[_0x8f389b(0x243)+_0xf40849[_0x8f389b(0x17d)]()]){if(_0x3c14da++,_0x11690b[_0x8f389b(0x181)]++,_0x3c14da>_0x56475e){_0x5c833e=!0x0;break;}if(!_0x11690b[_0x8f389b(0x1b4)]&&_0x11690b[_0x8f389b(0x206)]&&_0x11690b[_0x8f389b(0x181)]>_0x11690b[_0x8f389b(0x1e3)]){_0x5c833e=!0x0;break;}_0x2c89d6[_0x8f389b(0x15f)](_0x552ebb[_0x8f389b(0x1cb)](_0x436656,_0x1d475d,_0x355719,_0xfddba0,_0xf40849,_0x11690b));}}}}}if(_0x3b41ea[_0x8f389b(0x1af)]=_0xfddba0,_0x55388d?(_0x3b41ea[_0x8f389b(0x22b)]=_0x355719[_0x8f389b(0x19d)](),this[_0x8f389b(0x20b)](_0xfddba0,_0x3b41ea,_0x11690b,_0x5dcf20)):_0xfddba0===_0x8f389b(0x17e)?_0x3b41ea[_0x8f389b(0x22b)]=this[_0x8f389b(0x18e)]['call'](_0x355719):_0xfddba0===_0x8f389b(0x17c)?_0x3b41ea[_0x8f389b(0x22b)]=_0x355719['toString']():_0xfddba0===_0x8f389b(0x1c9)?_0x3b41ea[_0x8f389b(0x22b)]=this[_0x8f389b(0x179)]['call'](_0x355719):_0xfddba0===_0x8f389b(0x205)&&this[_0x8f389b(0x22e)]?_0x3b41ea['value']=this[_0x8f389b(0x22e)][_0x8f389b(0x217)][_0x8f389b(0x17d)][_0x8f389b(0x174)](_0x355719):!_0x11690b[_0x8f389b(0x247)]&&!(_0xfddba0===_0x8f389b(0x1e8)||_0xfddba0==='undefined')&&(delete _0x3b41ea[_0x8f389b(0x22b)],_0x3b41ea[_0x8f389b(0x215)]=!0x0),_0x5c833e&&(_0x3b41ea['cappedProps']=!0x0),_0x1dfe61=_0x11690b[_0x8f389b(0x229)][_0x8f389b(0x1a1)],_0x11690b[_0x8f389b(0x229)][_0x8f389b(0x1a1)]=_0x3b41ea,this[_0x8f389b(0x195)](_0x3b41ea,_0x11690b),_0x2c89d6[_0x8f389b(0x1b5)]){for(_0x461263=0x0,_0x2cdc9e=_0x2c89d6['length'];_0x461263<_0x2cdc9e;_0x461263++)_0x2c89d6[_0x461263](_0x461263);}_0x436656[_0x8f389b(0x1b5)]&&(_0x3b41ea[_0x8f389b(0x1f9)]=_0x436656);}catch(_0x23ea81){_0x4900e1(_0x23ea81,_0x3b41ea,_0x11690b);}return this['_additionalMetadata'](_0x355719,_0x3b41ea),this['_treeNodePropertiesAfterFullValue'](_0x3b41ea,_0x11690b),_0x11690b[_0x8f389b(0x229)][_0x8f389b(0x1a1)]=_0x1dfe61,_0x11690b[_0x8f389b(0x197)]--,_0x11690b[_0x8f389b(0x206)]=_0x236687,_0x11690b[_0x8f389b(0x206)]&&_0x11690b[_0x8f389b(0x20f)][_0x8f389b(0x172)](),_0x3b41ea;}[_0x47a0b2(0x1a5)](_0x1df297){return Object['getOwnPropertySymbols']?Object['getOwnPropertySymbols'](_0x1df297):[];}[_0x47a0b2(0x1dc)](_0xe328fa){var _0xc71172=_0x47a0b2;return!!(_0xe328fa&&_0x55706b['Set']&&this[_0xc71172(0x164)](_0xe328fa)===_0xc71172(0x1d3)&&_0xe328fa[_0xc71172(0x1e6)]);}['_blacklistedProperty'](_0x27c689,_0x49a238,_0x3a7a1c){var _0x47e669=_0x47a0b2;return _0x3a7a1c[_0x47e669(0x1e7)]?typeof _0x27c689[_0x49a238]==_0x47e669(0x182):!0x1;}[_0x47a0b2(0x169)](_0x28a592){var _0x47f751=_0x47a0b2,_0x180e49='';return _0x180e49=typeof _0x28a592,_0x180e49===_0x47f751(0x162)?this[_0x47f751(0x164)](_0x28a592)===_0x47f751(0x15d)?_0x180e49=_0x47f751(0x1b0):this[_0x47f751(0x164)](_0x28a592)===_0x47f751(0x1ea)?_0x180e49=_0x47f751(0x17e):this[_0x47f751(0x164)](_0x28a592)===_0x47f751(0x15a)?_0x180e49=_0x47f751(0x17c):_0x28a592===null?_0x180e49=_0x47f751(0x1e8):_0x28a592['constructor']&&(_0x180e49=_0x28a592[_0x47f751(0x18d)][_0x47f751(0x23d)]||_0x180e49):_0x180e49==='undefined'&&this[_0x47f751(0x15e)]&&_0x28a592 instanceof this[_0x47f751(0x15e)]&&(_0x180e49=_0x47f751(0x244)),_0x180e49;}[_0x47a0b2(0x164)](_0x2fcd7b){var _0x1fcd42=_0x47a0b2;return Object[_0x1fcd42(0x217)][_0x1fcd42(0x17d)][_0x1fcd42(0x174)](_0x2fcd7b);}['_isPrimitiveType'](_0x44e5b5){var _0x556962=_0x47a0b2;return _0x44e5b5==='boolean'||_0x44e5b5===_0x556962(0x23a)||_0x44e5b5===_0x556962(0x1f3);}[_0x47a0b2(0x19f)](_0x25dc08){var _0x1b66e9=_0x47a0b2;return _0x25dc08===_0x1b66e9(0x1ce)||_0x25dc08===_0x1b66e9(0x22f)||_0x25dc08===_0x1b66e9(0x187);}[_0x47a0b2(0x1b3)](_0x133410,_0xe3d199,_0x36eaca,_0x3ae903,_0x310148,_0xd2268){var _0xceeda1=this;return function(_0x39264e){var _0x3380ba=_0x5d6a,_0x9875f4=_0x310148['node'][_0x3380ba(0x1a1)],_0x104af8=_0x310148[_0x3380ba(0x229)][_0x3380ba(0x1d8)],_0x2f412a=_0x310148['node'][_0x3380ba(0x223)];_0x310148[_0x3380ba(0x229)][_0x3380ba(0x223)]=_0x9875f4,_0x310148[_0x3380ba(0x229)][_0x3380ba(0x1d8)]=typeof _0x3ae903==_0x3380ba(0x1f3)?_0x3ae903:_0x39264e,_0x133410[_0x3380ba(0x15f)](_0xceeda1['_property'](_0xe3d199,_0x36eaca,_0x3ae903,_0x310148,_0xd2268)),_0x310148[_0x3380ba(0x229)]['parent']=_0x2f412a,_0x310148[_0x3380ba(0x229)]['index']=_0x104af8;};}[_0x47a0b2(0x1cb)](_0x5d3084,_0x541edd,_0x57c233,_0xebce12,_0x414960,_0x375230,_0x53d46b){var _0x19d958=_0x47a0b2,_0x13f36a=this;return _0x541edd[_0x19d958(0x243)+_0x414960['toString']()]=!0x0,function(_0x1335af){var _0x4470b3=_0x19d958,_0x7413fe=_0x375230['node'][_0x4470b3(0x1a1)],_0x354496=_0x375230[_0x4470b3(0x229)][_0x4470b3(0x1d8)],_0x4c2dcb=_0x375230[_0x4470b3(0x229)][_0x4470b3(0x223)];_0x375230[_0x4470b3(0x229)][_0x4470b3(0x223)]=_0x7413fe,_0x375230['node'][_0x4470b3(0x1d8)]=_0x1335af,_0x5d3084[_0x4470b3(0x15f)](_0x13f36a[_0x4470b3(0x18a)](_0x57c233,_0xebce12,_0x414960,_0x375230,_0x53d46b)),_0x375230[_0x4470b3(0x229)][_0x4470b3(0x223)]=_0x4c2dcb,_0x375230[_0x4470b3(0x229)][_0x4470b3(0x1d8)]=_0x354496;};}[_0x47a0b2(0x18a)](_0x2637e2,_0x414106,_0x2368f3,_0x3dd70e,_0xb04b6f){var _0x2c00c8=_0x47a0b2,_0x1619e5=this;_0xb04b6f||(_0xb04b6f=function(_0x26680a,_0x1e7dd1){return _0x26680a[_0x1e7dd1];});var _0xa76935=_0x2368f3[_0x2c00c8(0x17d)](),_0x4452e9=_0x3dd70e['expressionsToEvaluate']||{},_0x128e56=_0x3dd70e[_0x2c00c8(0x247)],_0x367daf=_0x3dd70e['isExpressionToEvaluate'];try{var _0x32b3c4=this[_0x2c00c8(0x1bb)](_0x2637e2),_0x3f3022=_0xa76935;_0x32b3c4&&_0x3f3022[0x0]==='\\x27'&&(_0x3f3022=_0x3f3022[_0x2c00c8(0x1c7)](0x1,_0x3f3022['length']-0x2));var _0x3fe7ed=_0x3dd70e[_0x2c00c8(0x1ac)]=_0x4452e9[_0x2c00c8(0x243)+_0x3f3022];_0x3fe7ed&&(_0x3dd70e['depth']=_0x3dd70e[_0x2c00c8(0x247)]+0x1),_0x3dd70e[_0x2c00c8(0x1b4)]=!!_0x3fe7ed;var _0x50e270=typeof _0x2368f3==_0x2c00c8(0x205),_0x2570fd={'name':_0x50e270||_0x32b3c4?_0xa76935:this[_0x2c00c8(0x19a)](_0xa76935)};if(_0x50e270&&(_0x2570fd['symbol']=!0x0),!(_0x414106===_0x2c00c8(0x1b0)||_0x414106===_0x2c00c8(0x17f))){var _0x5d0ca8=this[_0x2c00c8(0x194)](_0x2637e2,_0x2368f3);if(_0x5d0ca8&&(_0x5d0ca8[_0x2c00c8(0x1f4)]&&(_0x2570fd[_0x2c00c8(0x1d2)]=!0x0),_0x5d0ca8[_0x2c00c8(0x220)]&&!_0x3fe7ed&&!_0x3dd70e[_0x2c00c8(0x21a)]))return _0x2570fd[_0x2c00c8(0x1d9)]=!0x0,this[_0x2c00c8(0x1ef)](_0x2570fd,_0x3dd70e),_0x2570fd;}var _0x23501f;try{_0x23501f=_0xb04b6f(_0x2637e2,_0x2368f3);}catch(_0x58a116){return _0x2570fd={'name':_0xa76935,'type':_0x2c00c8(0x1cf),'error':_0x58a116['message']},this[_0x2c00c8(0x1ef)](_0x2570fd,_0x3dd70e),_0x2570fd;}var _0x25e7bd=this[_0x2c00c8(0x169)](_0x23501f),_0x4d1b0a=this[_0x2c00c8(0x23b)](_0x25e7bd);if(_0x2570fd[_0x2c00c8(0x1af)]=_0x25e7bd,_0x4d1b0a)this[_0x2c00c8(0x1ef)](_0x2570fd,_0x3dd70e,_0x23501f,function(){var _0x471d69=_0x2c00c8;_0x2570fd['value']=_0x23501f['valueOf'](),!_0x3fe7ed&&_0x1619e5[_0x471d69(0x20b)](_0x25e7bd,_0x2570fd,_0x3dd70e,{});});else{var _0x590ad9=_0x3dd70e[_0x2c00c8(0x206)]&&_0x3dd70e[_0x2c00c8(0x197)]<_0x3dd70e[_0x2c00c8(0x1a2)]&&_0x3dd70e['autoExpandPreviousObjects'][_0x2c00c8(0x160)](_0x23501f)<0x0&&_0x25e7bd!=='function'&&_0x3dd70e[_0x2c00c8(0x181)]<_0x3dd70e[_0x2c00c8(0x1e3)];_0x590ad9||_0x3dd70e[_0x2c00c8(0x197)]<_0x128e56||_0x3fe7ed?(this['serialize'](_0x2570fd,_0x23501f,_0x3dd70e,_0x3fe7ed||{}),this[_0x2c00c8(0x1c8)](_0x23501f,_0x2570fd)):this[_0x2c00c8(0x1ef)](_0x2570fd,_0x3dd70e,_0x23501f,function(){var _0x1e4055=_0x2c00c8;_0x25e7bd===_0x1e4055(0x1e8)||_0x25e7bd===_0x1e4055(0x241)||(delete _0x2570fd[_0x1e4055(0x22b)],_0x2570fd['capped']=!0x0);});}return _0x2570fd;}finally{_0x3dd70e[_0x2c00c8(0x1ac)]=_0x4452e9,_0x3dd70e[_0x2c00c8(0x247)]=_0x128e56,_0x3dd70e[_0x2c00c8(0x1b4)]=_0x367daf;}}[_0x47a0b2(0x20b)](_0x4e451c,_0x23df6f,_0x406341,_0x39492b){var _0x1f7aa3=_0x47a0b2,_0x149066=_0x39492b[_0x1f7aa3(0x204)]||_0x406341[_0x1f7aa3(0x204)];if((_0x4e451c===_0x1f7aa3(0x23a)||_0x4e451c===_0x1f7aa3(0x22f))&&_0x23df6f['value']){let _0x7e7895=_0x23df6f[_0x1f7aa3(0x22b)][_0x1f7aa3(0x1b5)];_0x406341[_0x1f7aa3(0x1e1)]+=_0x7e7895,_0x406341['allStrLength']>_0x406341[_0x1f7aa3(0x166)]?(_0x23df6f[_0x1f7aa3(0x215)]='',delete _0x23df6f[_0x1f7aa3(0x22b)]):_0x7e7895>_0x149066&&(_0x23df6f[_0x1f7aa3(0x215)]=_0x23df6f[_0x1f7aa3(0x22b)][_0x1f7aa3(0x1c7)](0x0,_0x149066),delete _0x23df6f[_0x1f7aa3(0x22b)]);}}[_0x47a0b2(0x1bb)](_0x23cdcc){var _0x256062=_0x47a0b2;return!!(_0x23cdcc&&_0x55706b[_0x256062(0x193)]&&this[_0x256062(0x164)](_0x23cdcc)===_0x256062(0x1bf)&&_0x23cdcc[_0x256062(0x1e6)]);}[_0x47a0b2(0x19a)](_0x3c2079){var _0x246e5f=_0x47a0b2;if(_0x3c2079[_0x246e5f(0x188)](/^\\d+$/))return _0x3c2079;var _0x9c3b7c;try{_0x9c3b7c=JSON[_0x246e5f(0x23f)](''+_0x3c2079);}catch{_0x9c3b7c='\\x22'+this['_objectToString'](_0x3c2079)+'\\x22';}return _0x9c3b7c[_0x246e5f(0x188)](/^\"([a-zA-Z_][a-zA-Z_0-9]*)\"$/)?_0x9c3b7c=_0x9c3b7c[_0x246e5f(0x1c7)](0x1,_0x9c3b7c[_0x246e5f(0x1b5)]-0x2):_0x9c3b7c=_0x9c3b7c['replace'](/'/g,'\\x5c\\x27')[_0x246e5f(0x1e9)](/\\\\\"/g,'\\x22')[_0x246e5f(0x1e9)](/(^\"|\"$)/g,'\\x27'),_0x9c3b7c;}[_0x47a0b2(0x1ef)](_0x35bd33,_0x4d9463,_0x3fc71f,_0xddd4eb){var _0x4e6cde=_0x47a0b2;this[_0x4e6cde(0x195)](_0x35bd33,_0x4d9463),_0xddd4eb&&_0xddd4eb(),this[_0x4e6cde(0x1c8)](_0x3fc71f,_0x35bd33),this['_treeNodePropertiesAfterFullValue'](_0x35bd33,_0x4d9463);}[_0x47a0b2(0x195)](_0x4ac2ef,_0x590213){var _0x43b32a=_0x47a0b2;this[_0x43b32a(0x20d)](_0x4ac2ef,_0x590213),this[_0x43b32a(0x202)](_0x4ac2ef,_0x590213),this['_setNodeExpressionPath'](_0x4ac2ef,_0x590213),this[_0x43b32a(0x1fb)](_0x4ac2ef,_0x590213);}[_0x47a0b2(0x20d)](_0x44e2cf,_0x75d4fd){}[_0x47a0b2(0x202)](_0x205d60,_0x3b6509){}[_0x47a0b2(0x1e5)](_0x3ff3ad,_0x22b8f8){}[_0x47a0b2(0x196)](_0x36cbf9){var _0x95bfd2=_0x47a0b2;return _0x36cbf9===this[_0x95bfd2(0x24b)];}['_treeNodePropertiesAfterFullValue'](_0x5468d3,_0x5a6192){var _0x4d99f6=_0x47a0b2;this[_0x4d99f6(0x1e5)](_0x5468d3,_0x5a6192),this[_0x4d99f6(0x242)](_0x5468d3),_0x5a6192[_0x4d99f6(0x1ad)]&&this[_0x4d99f6(0x1f2)](_0x5468d3),this[_0x4d99f6(0x1a6)](_0x5468d3,_0x5a6192),this[_0x4d99f6(0x222)](_0x5468d3,_0x5a6192),this[_0x4d99f6(0x211)](_0x5468d3);}[_0x47a0b2(0x1c8)](_0x31bef7,_0xca3dfa){var _0x4bb0cb=_0x47a0b2;let _0x38ab33;try{_0x55706b['console']&&(_0x38ab33=_0x55706b[_0x4bb0cb(0x1ae)][_0x4bb0cb(0x1bd)],_0x55706b[_0x4bb0cb(0x1ae)][_0x4bb0cb(0x1bd)]=function(){}),_0x31bef7&&typeof _0x31bef7[_0x4bb0cb(0x1b5)]==_0x4bb0cb(0x1f3)&&(_0xca3dfa[_0x4bb0cb(0x1b5)]=_0x31bef7[_0x4bb0cb(0x1b5)]);}catch{}finally{_0x38ab33&&(_0x55706b[_0x4bb0cb(0x1ae)][_0x4bb0cb(0x1bd)]=_0x38ab33);}if(_0xca3dfa[_0x4bb0cb(0x1af)]===_0x4bb0cb(0x1f3)||_0xca3dfa[_0x4bb0cb(0x1af)]===_0x4bb0cb(0x187)){if(isNaN(_0xca3dfa[_0x4bb0cb(0x22b)]))_0xca3dfa[_0x4bb0cb(0x198)]=!0x0,delete _0xca3dfa['value'];else switch(_0xca3dfa['value']){case Number[_0x4bb0cb(0x1a9)]:_0xca3dfa['positiveInfinity']=!0x0,delete _0xca3dfa[_0x4bb0cb(0x22b)];break;case Number['NEGATIVE_INFINITY']:_0xca3dfa['negativeInfinity']=!0x0,delete _0xca3dfa[_0x4bb0cb(0x22b)];break;case 0x0:this[_0x4bb0cb(0x1f8)](_0xca3dfa[_0x4bb0cb(0x22b)])&&(_0xca3dfa[_0x4bb0cb(0x201)]=!0x0);break;}}else _0xca3dfa[_0x4bb0cb(0x1af)]===_0x4bb0cb(0x182)&&typeof _0x31bef7[_0x4bb0cb(0x23d)]=='string'&&_0x31bef7[_0x4bb0cb(0x23d)]&&_0xca3dfa[_0x4bb0cb(0x23d)]&&_0x31bef7[_0x4bb0cb(0x23d)]!==_0xca3dfa[_0x4bb0cb(0x23d)]&&(_0xca3dfa[_0x4bb0cb(0x1f7)]=_0x31bef7[_0x4bb0cb(0x23d)]);}[_0x47a0b2(0x1f8)](_0x53e7ab){return 0x1/_0x53e7ab===Number['NEGATIVE_INFINITY'];}[_0x47a0b2(0x1f2)](_0xc0b002){var _0xedc6a3=_0x47a0b2;!_0xc0b002['props']||!_0xc0b002[_0xedc6a3(0x1f9)]['length']||_0xc0b002[_0xedc6a3(0x1af)]===_0xedc6a3(0x1b0)||_0xc0b002[_0xedc6a3(0x1af)]===_0xedc6a3(0x193)||_0xc0b002[_0xedc6a3(0x1af)]===_0xedc6a3(0x165)||_0xc0b002[_0xedc6a3(0x1f9)]['sort'](function(_0x1708fa,_0x5f500b){var _0x160fb6=_0xedc6a3,_0x47c3f7=_0x1708fa['name'][_0x160fb6(0x1ee)](),_0x3eba78=_0x5f500b['name'][_0x160fb6(0x1ee)]();return _0x47c3f7<_0x3eba78?-0x1:_0x47c3f7>_0x3eba78?0x1:0x0;});}['_addFunctionsNode'](_0x38ed93,_0xc52bd8){var _0x5f5c32=_0x47a0b2;if(!(_0xc52bd8['noFunctions']||!_0x38ed93[_0x5f5c32(0x1f9)]||!_0x38ed93[_0x5f5c32(0x1f9)]['length'])){for(var _0x1f842a=[],_0x3c42af=[],_0x2f2dcf=0x0,_0x429b2c=_0x38ed93[_0x5f5c32(0x1f9)][_0x5f5c32(0x1b5)];_0x2f2dcf<_0x429b2c;_0x2f2dcf++){var _0x39c475=_0x38ed93[_0x5f5c32(0x1f9)][_0x2f2dcf];_0x39c475[_0x5f5c32(0x1af)]===_0x5f5c32(0x182)?_0x1f842a[_0x5f5c32(0x15f)](_0x39c475):_0x3c42af[_0x5f5c32(0x15f)](_0x39c475);}if(!(!_0x3c42af[_0x5f5c32(0x1b5)]||_0x1f842a[_0x5f5c32(0x1b5)]<=0x1)){_0x38ed93[_0x5f5c32(0x1f9)]=_0x3c42af;var _0x28a189={'functionsNode':!0x0,'props':_0x1f842a};this[_0x5f5c32(0x20d)](_0x28a189,_0xc52bd8),this[_0x5f5c32(0x1e5)](_0x28a189,_0xc52bd8),this[_0x5f5c32(0x242)](_0x28a189),this[_0x5f5c32(0x1fb)](_0x28a189,_0xc52bd8),_0x28a189['id']+='\\x20f',_0x38ed93['props'][_0x5f5c32(0x17a)](_0x28a189);}}}[_0x47a0b2(0x222)](_0x36de79,_0x4554f4){}[_0x47a0b2(0x242)](_0x48af8c){}[_0x47a0b2(0x16b)](_0x4d8ed5){var _0x2f5c0b=_0x47a0b2;return Array[_0x2f5c0b(0x1fa)](_0x4d8ed5)||typeof _0x4d8ed5=='object'&&this['_objectToString'](_0x4d8ed5)==='[object\\x20Array]';}['_setNodePermissions'](_0x2e6424,_0x2e0467){}['_cleanNode'](_0x5ec349){var _0x315d63=_0x47a0b2;delete _0x5ec349[_0x315d63(0x232)],delete _0x5ec349['_hasSetOnItsPath'],delete _0x5ec349[_0x315d63(0x1d6)];}[_0x47a0b2(0x1bc)](_0x5d5654,_0x3e7605){}}let _0x23fb49=new _0x579afe(),_0x3870df={'props':0x64,'elements':0x64,'strLength':0x400*0x32,'totalStrLength':0x400*0x32,'autoExpandLimit':0x1388,'autoExpandMaxDepth':0xa},_0x293e67={'props':0x5,'elements':0x5,'strLength':0x100,'totalStrLength':0x100*0x3,'autoExpandLimit':0x1e,'autoExpandMaxDepth':0x2};function _0x1da4fa(_0x6c245c,_0x8223f4,_0x41c6d3,_0xe75f6f,_0x5212d1,_0x4f3ab2){var _0x4b6b36=_0x47a0b2;let _0x5b0918,_0x5104a5;try{_0x5104a5=_0x2c2b75(),_0x5b0918=_0x3c5897[_0x8223f4],!_0x5b0918||_0x5104a5-_0x5b0918['ts']>0x1f4&&_0x5b0918['count']&&_0x5b0918['time']/_0x5b0918['count']<0x64?(_0x3c5897[_0x8223f4]=_0x5b0918={'count':0x0,'time':0x0,'ts':_0x5104a5},_0x3c5897[_0x4b6b36(0x175)]={}):_0x5104a5-_0x3c5897[_0x4b6b36(0x175)]['ts']>0x32&&_0x3c5897['hits'][_0x4b6b36(0x1d0)]&&_0x3c5897[_0x4b6b36(0x175)][_0x4b6b36(0x170)]/_0x3c5897[_0x4b6b36(0x175)]['count']<0x64&&(_0x3c5897[_0x4b6b36(0x175)]={});let _0x34cbe3=[],_0x406a4a=_0x5b0918[_0x4b6b36(0x210)]||_0x3c5897[_0x4b6b36(0x175)][_0x4b6b36(0x210)]?_0x293e67:_0x3870df,_0x42f538=_0x2ab881=>{var _0x20601f=_0x4b6b36;let _0x5d8074={};return _0x5d8074[_0x20601f(0x1f9)]=_0x2ab881[_0x20601f(0x1f9)],_0x5d8074[_0x20601f(0x1ba)]=_0x2ab881[_0x20601f(0x1ba)],_0x5d8074['strLength']=_0x2ab881[_0x20601f(0x204)],_0x5d8074[_0x20601f(0x166)]=_0x2ab881[_0x20601f(0x166)],_0x5d8074[_0x20601f(0x1e3)]=_0x2ab881['autoExpandLimit'],_0x5d8074[_0x20601f(0x1a2)]=_0x2ab881[_0x20601f(0x1a2)],_0x5d8074[_0x20601f(0x1ad)]=!0x1,_0x5d8074[_0x20601f(0x1e7)]=!_0x1c78da,_0x5d8074[_0x20601f(0x247)]=0x1,_0x5d8074[_0x20601f(0x197)]=0x0,_0x5d8074['expId']=_0x20601f(0x180),_0x5d8074['rootExpression']=_0x20601f(0x213),_0x5d8074['autoExpand']=!0x0,_0x5d8074[_0x20601f(0x20f)]=[],_0x5d8074[_0x20601f(0x181)]=0x0,_0x5d8074[_0x20601f(0x21a)]=!0x0,_0x5d8074[_0x20601f(0x1e1)]=0x0,_0x5d8074[_0x20601f(0x229)]={'current':void 0x0,'parent':void 0x0,'index':0x0},_0x5d8074;};for(var _0x3df8ae=0x0;_0x3df8ae<_0x5212d1[_0x4b6b36(0x1b5)];_0x3df8ae++)_0x34cbe3[_0x4b6b36(0x15f)](_0x23fb49[_0x4b6b36(0x238)]({'timeNode':_0x6c245c===_0x4b6b36(0x170)||void 0x0},_0x5212d1[_0x3df8ae],_0x42f538(_0x406a4a),{}));if(_0x6c245c==='trace'){let _0x38d794=Error[_0x4b6b36(0x20a)];try{Error['stackTraceLimit']=0x1/0x0,_0x34cbe3[_0x4b6b36(0x15f)](_0x23fb49[_0x4b6b36(0x238)]({'stackNode':!0x0},new Error()['stack'],_0x42f538(_0x406a4a),{'strLength':0x1/0x0}));}finally{Error[_0x4b6b36(0x20a)]=_0x38d794;}}return{'method':'log','version':_0x4aacad,'args':[{'ts':_0x41c6d3,'session':_0xe75f6f,'args':_0x34cbe3,'id':_0x8223f4,'context':_0x4f3ab2}]};}catch(_0x7fb702){return{'method':'log','version':_0x4aacad,'args':[{'ts':_0x41c6d3,'session':_0xe75f6f,'args':[{'type':_0x4b6b36(0x1cf),'error':_0x7fb702&&_0x7fb702[_0x4b6b36(0x20e)]}],'id':_0x8223f4,'context':_0x4f3ab2}]};}finally{try{if(_0x5b0918&&_0x5104a5){let _0x65e00f=_0x2c2b75();_0x5b0918[_0x4b6b36(0x1d0)]++,_0x5b0918[_0x4b6b36(0x170)]+=_0x4490a8(_0x5104a5,_0x65e00f),_0x5b0918['ts']=_0x65e00f,_0x3c5897['hits']['count']++,_0x3c5897['hits'][_0x4b6b36(0x170)]+=_0x4490a8(_0x5104a5,_0x65e00f),_0x3c5897[_0x4b6b36(0x175)]['ts']=_0x65e00f,(_0x5b0918[_0x4b6b36(0x1d0)]>0x32||_0x5b0918[_0x4b6b36(0x170)]>0x64)&&(_0x5b0918[_0x4b6b36(0x210)]=!0x0),(_0x3c5897[_0x4b6b36(0x175)]['count']>0x3e8||_0x3c5897[_0x4b6b36(0x175)][_0x4b6b36(0x170)]>0x12c)&&(_0x3c5897[_0x4b6b36(0x175)][_0x4b6b36(0x210)]=!0x0);}}catch{}}}return _0x1da4fa;}((_0x3be010,_0x1c6083,_0x1c7318,_0x4acc8b,_0x4a0935,_0x44dd85,_0x2fc444,_0x9060b8,_0x49911f,_0x462ba4,_0x3b3d5c)=>{var _0x11fbd2=_0x29ef0d;if(_0x3be010[_0x11fbd2(0x1aa)])return _0x3be010['_console_ninja'];if(!X(_0x3be010,_0x9060b8,_0x4a0935))return _0x3be010[_0x11fbd2(0x1aa)]={'consoleLog':()=>{},'consoleTrace':()=>{},'consoleTime':()=>{},'consoleTimeEnd':()=>{},'autoLog':()=>{},'autoLogMany':()=>{},'autoTraceMany':()=>{},'coverage':()=>{},'autoTrace':()=>{},'autoTime':()=>{},'autoTimeEnd':()=>{}},_0x3be010[_0x11fbd2(0x1aa)];let _0x50a784=b(_0x3be010),_0x40f429=_0x50a784[_0x11fbd2(0x167)],_0x36b757=_0x50a784[_0x11fbd2(0x186)],_0x43295d=_0x50a784['now'],_0x25708c={'hits':{},'ts':{}},_0x2b9c69=H(_0x3be010,_0x49911f,_0x25708c,_0x44dd85),_0x1c8945=_0x2a3a63=>{_0x25708c['ts'][_0x2a3a63]=_0x36b757();},_0x22f50a=(_0x5ddb14,_0x238007)=>{var _0x54cf06=_0x11fbd2;let _0x5a1ef7=_0x25708c['ts'][_0x238007];if(delete _0x25708c['ts'][_0x238007],_0x5a1ef7){let _0x109dbe=_0x40f429(_0x5a1ef7,_0x36b757());_0x4be584(_0x2b9c69(_0x54cf06(0x170),_0x5ddb14,_0x43295d(),_0x34c91e,[_0x109dbe],_0x238007));}},_0x385606=_0x3b7983=>{var _0x4105cb=_0x11fbd2,_0x927eed;return _0x4a0935===_0x4105cb(0x245)&&_0x3be010[_0x4105cb(0x240)]&&((_0x927eed=_0x3b7983==null?void 0x0:_0x3b7983['args'])==null?void 0x0:_0x927eed[_0x4105cb(0x1b5)])&&(_0x3b7983[_0x4105cb(0x18b)][0x0][_0x4105cb(0x240)]=_0x3be010[_0x4105cb(0x240)]),_0x3b7983;};_0x3be010[_0x11fbd2(0x1aa)]={'consoleLog':(_0x2aa544,_0x2ff27a)=>{var _0x2a9c07=_0x11fbd2;_0x3be010[_0x2a9c07(0x1ae)][_0x2a9c07(0x1a8)]['name']!==_0x2a9c07(0x207)&&_0x4be584(_0x2b9c69(_0x2a9c07(0x1a8),_0x2aa544,_0x43295d(),_0x34c91e,_0x2ff27a));},'consoleTrace':(_0x286a1f,_0x5cf0b5)=>{var _0x290f4c=_0x11fbd2;_0x3be010[_0x290f4c(0x1ae)][_0x290f4c(0x1a8)][_0x290f4c(0x23d)]!==_0x290f4c(0x227)&&_0x4be584(_0x385606(_0x2b9c69('trace',_0x286a1f,_0x43295d(),_0x34c91e,_0x5cf0b5)));},'consoleTime':_0x4f2cd8=>{_0x1c8945(_0x4f2cd8);},'consoleTimeEnd':(_0x16ebcf,_0x1ac98d)=>{_0x22f50a(_0x1ac98d,_0x16ebcf);},'autoLog':(_0x2fdc4b,_0x14c834)=>{var _0x3fd871=_0x11fbd2;_0x4be584(_0x2b9c69(_0x3fd871(0x1a8),_0x14c834,_0x43295d(),_0x34c91e,[_0x2fdc4b]));},'autoLogMany':(_0x51451c,_0x917f4e)=>{var _0x34e450=_0x11fbd2;_0x4be584(_0x2b9c69(_0x34e450(0x1a8),_0x51451c,_0x43295d(),_0x34c91e,_0x917f4e));},'autoTrace':(_0x1854e5,_0x464b23)=>{var _0x580941=_0x11fbd2;_0x4be584(_0x385606(_0x2b9c69(_0x580941(0x209),_0x464b23,_0x43295d(),_0x34c91e,[_0x1854e5])));},'autoTraceMany':(_0x1a33de,_0x14b400)=>{var _0x5134fb=_0x11fbd2;_0x4be584(_0x385606(_0x2b9c69(_0x5134fb(0x209),_0x1a33de,_0x43295d(),_0x34c91e,_0x14b400)));},'autoTime':(_0x47c325,_0x1c77d2,_0x5535e7)=>{_0x1c8945(_0x5535e7);},'autoTimeEnd':(_0x5b7f59,_0x3aad56,_0x31d876)=>{_0x22f50a(_0x3aad56,_0x31d876);},'coverage':_0x5b4371=>{var _0x56eed4=_0x11fbd2;_0x4be584({'method':_0x56eed4(0x184),'version':_0x44dd85,'args':[{'id':_0x5b4371}]});}};let _0x4be584=q(_0x3be010,_0x1c6083,_0x1c7318,_0x4acc8b,_0x4a0935,_0x462ba4,_0x3b3d5c),_0x34c91e=_0x3be010[_0x11fbd2(0x1fc)];return _0x3be010['_console_ninja'];})(globalThis,_0x29ef0d(0x1df),'34805',\"/home/wagner/.vscode/extensions/wallabyjs.console-ninja-1.0.323/node_modules\",'next.js','1.0.0',_0x29ef0d(0x16d),_0x29ef0d(0x225),_0x29ef0d(0x1ec),_0x29ef0d(0x1fd),_0x29ef0d(0x19c));");}catch(e){}};/* istanbul ignore next */function oo_oo(i,...v){try{oo_cm().consoleLog(i, v);}catch(e){} return v};/* istanbul ignore next */function oo_tr(i,...v){try{oo_cm().consoleTrace(i, v);}catch(e){} return v};/* istanbul ignore next */function oo_ts(v){try{oo_cm().consoleTime(v);}catch(e){} return v;};/* istanbul ignore next */function oo_te(v, i){try{oo_cm().consoleTimeEnd(v, i);}catch(e){} return v;};/*eslint unicorn/no-abusive-eslint-disable:,eslint-comments/disable-enable-pair:,eslint-comments/no-unlimited-disable:,eslint-comments/no-aggregating-enable:,eslint-comments/no-duplicate-disable:,eslint-comments/no-unused-disable:,eslint-comments/no-unused-enable:,*/