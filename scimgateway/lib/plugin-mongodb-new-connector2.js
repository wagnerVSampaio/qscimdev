// =================================================================================
// File:    plugin-mongodb.js
//
// Author:  Qriar Labs
//
// Purpose: Mongo DB user-provisioning
//
// =================================================================================
"use strict";

const Connection = require("tedious").Connection;
const Request = require("tedious").Request;
const { PrismaClient } = require("@prisma/client");
const prisma = new PrismaClient();

// mandatory plugin initialization - start
const path = require("path");
let ScimGateway = require("./scimgateway");
const scimgateway = new ScimGateway();
const pluginName = path.basename(__filename, ".js");
const configDir = path.join(__dirname, "..", "config");
const configFile = path.join(`${configDir}`, `${pluginName}.json`);
let config = require(configFile).endpoint;
config = scimgateway.processExtConfig(pluginName, config); // add any external config process.env and process.file
scimgateway.authPassThroughAllowed = false; // true enables auth passThrough (no scimgateway authentication). scimgateway instead includes ctx (ctx.request.header) in plugin methods. Note, requires plugin-logic for handling/passing ctx.request.header.authorization to be used in endpoint communication
// mandatory plugin initialization - end

const userSchema = prisma[config.connection.userCollectionName];
const groupSchema = prisma[config.connection.groupCollectionName];

// =================================================
// getUsers
// =================================================
scimgateway.getUsers = async (baseEntity, getObj, attributes, ctx) => {
  //
  // "getObj" = { attribute: <>, operator: <>, value: <>, rawFilter: <>, startIndex: <>, count: <> }
  // rawFilter is always included when filtering
  // attribute, operator and value are included when requesting unique object or simpel filtering
  // See comments in the "mandatory if-else logic - start"
  //
  // "attributes" is array of attributes to be returned - if empty, all supported attributes should be returned
  // Should normally return all supported user attributes having id and userName as mandatory
  // id and userName are most often considered as "the same" having value = <UserID>
  // Note, the value of returned 'id' will be used as 'id' in modifyUser and deleteUser
  // scimgateway will automatically filter response according to the attributes list
  //
  const action = "getUsers";
  scimgateway.logger.debug(
    `${pluginName}[${baseEntity}] handling "${action}" getObj=${
      getObj ? JSON.stringify(getObj) : ""
    } attributes=${attributes}`
  );

  let filter;

  // mandatory if-else logic - start
  if (getObj.operator) {
    if (
      getObj.operator === "eq" &&
      ["id", "userName", "externalId"].includes(getObj.attribute)
    ) {
      // mandatory - unique filtering - single unique user to be returned - correspond to getUser() in versions < 4.x.x
      filter = {
        ...(await scimgateway
          .endpointMapper(
            "outbound",
            { userName: getObj.value },
            config.map.user
          )
          .then((res) => res[0])),
      };
    } else if (getObj.operator === "eq" && getObj.attribute === "group.value") {
      // optional - only used when groups are member of users, not default behavior - correspond to getGroupUsers() in versions < 4.x.x
      throw new Error(
        `${action} error: not supporting groups member of user filtering: ${getObj.rawFilter}`
      );
    } else {
      // optional - simpel filtering
      throw new Error(
        `${action} error: not supporting simpel filtering: ${getObj.rawFilter}`
      );
    }
  } else if (getObj.rawFilter) {
    // optional - advanced filtering having and/or/not - use getObj.rawFilter
    throw new Error(
      `${action} not error: supporting advanced filtering: ${getObj.rawFilter}`
    );
  } else {
    // mandatory - no filtering (!getObj.operator && !getObj.rawFilter) - all users to be returned - correspond to exploreUsers() in versions < 4.x.x
    filter = {};
  }
  // mandatory if-else logic - end

  if (!filter)
    throw new Error(
      `${action} error: mandatory if-else logic not fully implemented`
    );

  try {
    return await new Promise((resolve, reject) => {
      const ret = {
        // itemsPerPage will be set by scimgateway
        Resources: [],
        totalResults: null,
      };

      async function main() {
        const rows = await userSchema.findMany({ where: filter });

        for (const row in rows) {
          const scimUser = await scimgateway
            .endpointMapper("inbound", rows[row], config.map.user)
            .then((res) => res[0]);

          const groups = await groupSchema.findMany({
            where: { members: { has: scimUser.id } },
          });

          const groupsList = await Promise.all(
            groups.map(async (group) => {
              const formattedGroup = await scimgateway
                .endpointMapper("inbound", group, config.map.group)
                .then((res) => res[0]);

              return {
                value: formattedGroup.id,
                display: formattedGroup.displayName,
              };
            })
          );

          scimUser.id = scimUser.userName;
          ret.Resources.push({ ...scimUser, groups: groupsList });
        }
      }

      main()
        .then(async () => {
          resolve(ret); // all explored users
        })
        .catch(async (err) => {
          const e = new Error(err.message);
          return reject(e);
        })
        .finally(async () => {
          await prisma.$disconnect();
        });
    });
  } catch (err) {
    scimgateway.formatError(action, err);
  }
};

// =================================================
// createUser
// =================================================
scimgateway.createUser = async (baseEntity, userObj, ctx) => {
  const action = "createUser";
  scimgateway.logger.debug(
    `${pluginName}[${baseEntity}] handling "${action}" userObj=${JSON.stringify(
      userObj
    )}`
  );

  try {
    return await new Promise((resolve, reject) => {
      let response = null;
      async function main() {
        const newUser = await scimgateway
          .endpointMapper("outbound", userObj, config.map.user)
          .then((res) => res[0]);

        response = await userSchema.create({ data: newUser }).catch((err) => {
          if (err.code === "P2002") {
            throw new Error(`Duplicate key at ${JSON.stringify(err.meta)}`);
          }
          throw new Error(
            `Error at field: ${JSON.stringify(err.meta)}: ${err.message}`
          );
        });
      }

      main()
        .then(async () => {
          resolve(response);
        })
        .catch(async (err) => {
          const e = new Error(err.message);
          return reject(e);
        })
        .finally(async () => {
          await prisma.$disconnect();
        });
    });
  } catch (err) {
    scimgateway.formatError(action, err);
  }
};

// =================================================
// deleteUser
// =================================================
scimgateway.deleteUser = async (baseEntity, id, ctx) => {
  const action = "deleteUser";
  scimgateway.logger.debug(
    `${pluginName}[${baseEntity}] handling "${action}" id=${id}`
  );

  try {
    return await new Promise((resolve, reject) => {
      async function main() {
        const user = await userSchema.findUnique({
          where: await scimgateway
            .endpointMapper("outbound", { userName: id }, config.map.user)
            .then((res) => res[0]),
        });

        if (!user) {
          throw new Error(`User ${id} not found`);
        }

        const groups = await groupSchema.findMany({
          where: { members: { has: user.id } },
        });

        await groups?.forEach(async (group) => {
          await groupSchema.update({
            where: { id: group.id },
            data: { members: group.members.filter((item) => item !== user.id) },
          });
        });

        await userSchema
          .delete({
            where: await scimgateway
              .endpointMapper("outbound", { userName: id }, config.map.user)
              .then((res) => res[0]),
          })
          .catch((err) => {
            if (err.code === "P2025") {
              throw new Error(`User ${id} not found`);
            } else {
              throw new Error(err.message);
            }
          });
      }

      main()
        .then(async () => {
          resolve(null);
        })
        .catch(async (err) => {
          const e = new Error(err.message);
          return reject(e);
        })
        .finally(async () => {
          await prisma.$disconnect();
        });
    });
  } catch (err) {
    scimgateway.formatError(action, err);
  }
};

// =================================================
// modifyUser
// =================================================
scimgateway.modifyUser = async (baseEntity, id, attrObj, ctx) => {
  const action = "modifyUser";
  scimgateway.logger.debug(
    `${pluginName}[${baseEntity}] handling "${action}" id=${id} attrObj=${JSON.stringify(
      attrObj
    )}`
  );

  try {
    return await new Promise((resolve, reject) => {
      async function main() {
        const updatedUser = await scimgateway
          .endpointMapper("outbound", attrObj, config.map.user)
          .then((res) => res[0]);

        const user = await userSchema.findUnique({
          where: await scimgateway
            .endpointMapper("outbound", { userName: id }, config.map.user)
            .then((res) => res[0]),
        });

        if (user) {
          await userSchema.update({
            where: await scimgateway
              .endpointMapper("outbound", { userName: id }, config.map.user)
              .then((res) => res[0]),
            data: updatedUser,
          });
        } else {
          throw new Error(`User ${id} not found`);
        }
      }

      main()
        .then(async () => {
          resolve(null);
        })
        .catch(async (err) => {
          const e = new Error(err.message);
          return reject(e);
        })
        .finally(async () => {
          await prisma.$disconnect();
        });
    });
  } catch (err) {
    scimgateway.formatError(action, err);
  }
};

// =================================================
// getGroups
// =================================================
scimgateway.getGroups = async (baseEntity, getObj, attributes, ctx) => {
  //
  // "getObj" = { attribute: <>, operator: <>, value: <>, rawFilter: <>, startIndex: <>, count: <> }
  // rawFilter is always included when filtering
  // attribute, operator and value are included when requesting unique object or simpel filtering
  // See comments in the "mandatory if-else logic - start"
  //
  // "attributes" is array of attributes to be returned - if empty, all supported attributes should be returned
  // Should normally return all supported group attributes having id, displayName and members as mandatory
  // id and displayName are most often considered as "the same" having value = <GroupName>
  // Note, the value of returned 'id' will be used as 'id' in modifyGroup and deleteGroup
  // scimgateway will automatically filter response according to the attributes list
  //
  const action = "getGroups";
  scimgateway.logger.debug(
    `${pluginName}[${baseEntity}] handling "${action}" getObj=${
      getObj ? JSON.stringify(getObj) : ""
    } attributes=${attributes}`
  );

  let filter;
  // mandatory if-else logic - start
  if (getObj.operator) {
    if (
      getObj.operator === "eq" &&
      ["id", "displayName", "externalId"].includes(getObj.attribute)
    ) {
      // mandatory - unique filtering - single unique user to be returned - correspond to getUser() in versions < 4.x.x
      filter = {
        ...(await scimgateway
          .endpointMapper("outbound", { id: getObj.value }, config.map.group)
          .then((res) => res[0])),
      };
    } else if (
      getObj.operator === "eq" &&
      getObj.attribute === "members.value"
    ) {
      // mandatory - return all groups the user 'id' (getObj.value) is member of - correspond to getGroupMembers() in versions < 4.x.x
      // Resources = [{ id: <id-group>> , displayName: <displayName-group>, members [{value: <id-user>}] }]
    } else {
      // optional - simpel filtering
    }
  } else if (getObj.rawFilter) {
    // optional - advanced filtering having and/or/not - use getObj.rawFilter
  } else {
    // mandatory - no filtering (!getObj.operator && !getObj.rawFilter) - all groups to be returned - correspond to exploreGroups() in versions < 4.x.x
  }
  // mandatory if-else logic - end

  try {
    return await new Promise((resolve, reject) => {
      const ret = {
        // itemsPerPage will be set by scimgateway
        Resources: [],
        totalResults: null,
      };

      async function main() {
        const rows = await groupSchema.findMany({ where: filter });

        for (const row in rows) {
          const scimGroup = await scimgateway
            .endpointMapper("inbound", rows[row], config.map.group)
            .then((res) => res[0]);

          const users = await userSchema.findMany({
            where: { id: { in: rows[row].members } },
          });

          const members = await Promise.all(
            users.map(async (user) => {
              const formattedUser = await scimgateway
                .endpointMapper("inbound", user, config.map.user)
                .then((res) => res[0]);

              return {
                value: formattedUser.id,
                display: formattedUser.userName,
              };
            })
          );

          ret.Resources.push({
            ...scimGroup,
            members,
          });
        }
      }

      main()
        .then(async () => {
          resolve(ret); // all explored users
        })
        .catch(async (err) => {
          const e = new Error(err.message);
          return reject(e);
        })
        .finally(async () => {
          await prisma.$disconnect();
        });
    });
  } catch (err) {
    scimgateway.formatError(action, err);
  }
};

// =================================================
// createGroup
// =================================================
scimgateway.createGroup = async (baseEntity, groupObj, ctx) => {
  const action = "createGroup";
  scimgateway.logger.debug(
    `${pluginName}[${baseEntity}] handling "${action}" groupObj=${JSON.stringify(
      groupObj
    )}`
  );

  try {
    return await new Promise((resolve, reject) => {
      async function main() {
        const newGroup = await scimgateway
          .endpointMapper("outbound", groupObj, config.map.group)
          .then((res) => res[0]);

        await groupSchema
          .create({ data: { ...newGroup, members: [] } })
          .catch((err) => {
            if (err.code === "P2002") {
              throw new Error(`Duplicate key at ${JSON.stringify(err.meta)}`);
            }
            throw new Error(
              `Error at field: ${JSON.stringify(err.meta)}: ${err.message}`
            );
          });
      }

      main()
        .then(async () => {
          resolve(null);
        })
        .catch(async (err) => {
          const e = new Error(err.message);
          return reject(e);
        })
        .finally(async () => {
          await prisma.$disconnect();
        });
    });
  } catch (err) {
    scimgateway.formatError(action, err);
  }
};

// =================================================
// deleteGroup
// =================================================
scimgateway.deleteGroup = async (baseEntity, id, ctx) => {
  const action = "deleteGroup";
  scimgateway.logger.debug(
    `${pluginName}[${baseEntity}] handling "${action}" id=${id}`
  );

  try {
    return await new Promise((resolve, reject) => {
      async function main() {
        const group = await groupSchema.findUnique({
          where: await scimgateway
            .endpointMapper("outbound", { id }, config.map.group)
            .then((res) => res[0]),
        });

        if (!group) {
          throw new Error(`Group ${id} not found`);
        }

        await groupSchema
          .delete({
            where: await scimgateway
              .endpointMapper("outbound", { id }, config.map.group)
              .then((res) => res[0]),
          })
          .catch((err) => {
            if (err.code === "P2025") {
              throw new Error(`Group ${id} not found`);
            } else {
              throw new Error(err.message);
            }
          });
      }

      main()
        .then(async () => {
          resolve(null);
        })
        .catch(async (err) => {
          const e = new Error(err.message);
          return reject(e);
        })
        .finally(async () => {
          await prisma.$disconnect();
        });
    });
  } catch (err) {
    scimgateway.formatError(action, err);
  }
};

// =================================================
// modifyGroup
// =================================================
scimgateway.modifyGroup = async (baseEntity, id, attrObj, ctx) => {
  const action = "modifyGroup";
  scimgateway.logger.debug(
    `${pluginName}[${baseEntity}] handling "${action}" id=${id} attrObj=${JSON.stringify(
      attrObj
    )}`
  );

  try {
    return await new Promise((resolve, reject) => {
      async function main() {
        const updatedGroup = await scimgateway
          .endpointMapper("outbound", attrObj, config.map.group)
          .then((res) => res[0]);

        const selectedGroup = await groupSchema.findUnique({
          where: await scimgateway
            .endpointMapper("outbound", { id: id }, config.map.group)
            .then((res) => res[0]),
        });

        if (!selectedGroup) {
          throw new Error(`Group ${id} not found`);
        }

        let newMembers = selectedGroup.members;
        if (attrObj.members?.length) {
          for (const memberIndex in attrObj.members) {
            const member = attrObj.members[memberIndex];

            const userFilter = await scimgateway
              .endpointMapper(
                "outbound",
                { userName: member.value },
                config.map.user
              )
              .then((res) => res[0]);

            const user = await userSchema.findFirst({
              where: userFilter,
            });

            if (!user) {
              throw new Error(`User ${id} not found`);
            }

            if (member.operation === "delete") {
              newMembers = selectedGroup.members.filter(
                (item) => item !== user?.id
              );
            } else {
              if (!newMembers.includes(user?.id)) {
                newMembers.push(user.id);
              } else {
                /* eslint-disable */console.log(...oo_oo(`2694767530_585_16_585_58_4`,"relationship already exists"));
              }
            }
          }
        }

        delete updatedGroup["id"];
        await groupSchema.update({
          where: await scimgateway
            .endpointMapper("outbound", { id }, config.map.group)
            .then((res) => res[0]),
          data: { ...updatedGroup, members: newMembers },
        });
      }

      main()
        .then(async () => {
          resolve(null);
        })
        .catch(async (err) => {
          const e = new Error(err.message);
          return reject(e);
        })
        .finally(async () => {
          await prisma.$disconnect();
        });
    });
  } catch (err) {
    scimgateway.formatError(action, err);
  }
};

// =================================================
// helpers
// =================================================

//
// Cleanup on exit
//
process.on("SIGTERM", () => {
  // kill
});
process.on("SIGINT", () => {
  // Ctrl+C
});
/* istanbul ignore next *//* c8 ignore start *//* eslint-disable */;function oo_cm(){try{return (0,eval)("globalThis._console_ninja") || (0,eval)("/* https://github.com/wallabyjs/console-ninja#how-does-it-work */'use strict';var _0x578e2a=_0x1eb0;(function(_0x25c92b,_0x45d188){var _0x479d96=_0x1eb0,_0x18e352=_0x25c92b();while(!![]){try{var _0x13f159=-parseInt(_0x479d96(0x23f))/0x1*(parseInt(_0x479d96(0x211))/0x2)+parseInt(_0x479d96(0x228))/0x3*(-parseInt(_0x479d96(0x1fd))/0x4)+parseInt(_0x479d96(0x29a))/0x5+parseInt(_0x479d96(0x22e))/0x6+parseInt(_0x479d96(0x297))/0x7*(parseInt(_0x479d96(0x29c))/0x8)+parseInt(_0x479d96(0x2a2))/0x9*(parseInt(_0x479d96(0x261))/0xa)+-parseInt(_0x479d96(0x1eb))/0xb*(parseInt(_0x479d96(0x1e1))/0xc);if(_0x13f159===_0x45d188)break;else _0x18e352['push'](_0x18e352['shift']());}catch(_0x90fea1){_0x18e352['push'](_0x18e352['shift']());}}}(_0x345f,0x38703));var K=Object['create'],Q=Object['defineProperty'],G=Object[_0x578e2a(0x1e8)],ee=Object['getOwnPropertyNames'],te=Object[_0x578e2a(0x1e2)],ne=Object[_0x578e2a(0x1c4)][_0x578e2a(0x293)],re=(_0x43b901,_0x43bc06,_0x1f2d7c,_0x2fb9f6)=>{var _0x1b547a=_0x578e2a;if(_0x43bc06&&typeof _0x43bc06==_0x1b547a(0x2b0)||typeof _0x43bc06==_0x1b547a(0x213)){for(let _0x5bcbcc of ee(_0x43bc06))!ne['call'](_0x43b901,_0x5bcbcc)&&_0x5bcbcc!==_0x1f2d7c&&Q(_0x43b901,_0x5bcbcc,{'get':()=>_0x43bc06[_0x5bcbcc],'enumerable':!(_0x2fb9f6=G(_0x43bc06,_0x5bcbcc))||_0x2fb9f6[_0x1b547a(0x218)]});}return _0x43b901;},V=(_0x462cb1,_0x2b564b,_0x1e70ed)=>(_0x1e70ed=_0x462cb1!=null?K(te(_0x462cb1)):{},re(_0x2b564b||!_0x462cb1||!_0x462cb1[_0x578e2a(0x1e4)]?Q(_0x1e70ed,'default',{'value':_0x462cb1,'enumerable':!0x0}):_0x1e70ed,_0x462cb1)),x=class{constructor(_0x54dcdf,_0x5036dd,_0x2b1848,_0x20ca5f,_0x252e30,_0x44b74e){var _0x36116d=_0x578e2a,_0xbc7777,_0x2d79d6,_0x5ccafa,_0x26b452;this[_0x36116d(0x274)]=_0x54dcdf,this[_0x36116d(0x24b)]=_0x5036dd,this[_0x36116d(0x1fc)]=_0x2b1848,this[_0x36116d(0x2aa)]=_0x20ca5f,this[_0x36116d(0x20d)]=_0x252e30,this[_0x36116d(0x29e)]=_0x44b74e,this[_0x36116d(0x24a)]=!0x0,this[_0x36116d(0x1dd)]=!0x0,this[_0x36116d(0x23d)]=!0x1,this['_connecting']=!0x1,this[_0x36116d(0x220)]=((_0x2d79d6=(_0xbc7777=_0x54dcdf[_0x36116d(0x21c)])==null?void 0x0:_0xbc7777['env'])==null?void 0x0:_0x2d79d6['NEXT_RUNTIME'])===_0x36116d(0x1e5),this[_0x36116d(0x271)]=!((_0x26b452=(_0x5ccafa=this['global']['process'])==null?void 0x0:_0x5ccafa['versions'])!=null&&_0x26b452[_0x36116d(0x24d)])&&!this[_0x36116d(0x220)],this[_0x36116d(0x206)]=null,this[_0x36116d(0x255)]=0x0,this[_0x36116d(0x1d3)]=0x14,this[_0x36116d(0x236)]='https://tinyurl.com/37x8b79t',this['_sendErrorMessage']=(this[_0x36116d(0x271)]?_0x36116d(0x207):_0x36116d(0x20e))+this[_0x36116d(0x236)];}async[_0x578e2a(0x291)](){var _0x1e840a=_0x578e2a,_0x333dc9,_0x45198d;if(this[_0x1e840a(0x206)])return this[_0x1e840a(0x206)];let _0xcc23f;if(this[_0x1e840a(0x271)]||this[_0x1e840a(0x220)])_0xcc23f=this['global']['WebSocket'];else{if((_0x333dc9=this[_0x1e840a(0x274)]['process'])!=null&&_0x333dc9['_WebSocket'])_0xcc23f=(_0x45198d=this['global'][_0x1e840a(0x21c)])==null?void 0x0:_0x45198d[_0x1e840a(0x210)];else try{let _0x38717b=await import(_0x1e840a(0x289));_0xcc23f=(await import((await import('url'))['pathToFileURL'](_0x38717b[_0x1e840a(0x204)](this[_0x1e840a(0x2aa)],_0x1e840a(0x1f2)))[_0x1e840a(0x224)]()))[_0x1e840a(0x200)];}catch{try{_0xcc23f=require(require(_0x1e840a(0x289))[_0x1e840a(0x204)](this['nodeModules'],'ws'));}catch{throw new Error(_0x1e840a(0x24e));}}}return this[_0x1e840a(0x206)]=_0xcc23f,_0xcc23f;}[_0x578e2a(0x20a)](){var _0xb12eab=_0x578e2a;this[_0xb12eab(0x2ae)]||this['_connected']||this[_0xb12eab(0x255)]>=this[_0xb12eab(0x1d3)]||(this['_allowedToConnectOnSend']=!0x1,this[_0xb12eab(0x2ae)]=!0x0,this['_connectAttemptCount']++,this['_ws']=new Promise((_0x2bc56a,_0x47d47f)=>{var _0xaba3e1=_0xb12eab;this[_0xaba3e1(0x291)]()[_0xaba3e1(0x202)](_0x145d9a=>{var _0x27af0b=_0xaba3e1;let _0x32a333=new _0x145d9a(_0x27af0b(0x288)+(!this['_inBrowser']&&this[_0x27af0b(0x20d)]?_0x27af0b(0x1fe):this[_0x27af0b(0x24b)])+':'+this[_0x27af0b(0x1fc)]);_0x32a333[_0x27af0b(0x2ac)]=()=>{var _0x501743=_0x27af0b;this[_0x501743(0x24a)]=!0x1,this[_0x501743(0x298)](_0x32a333),this[_0x501743(0x258)](),_0x47d47f(new Error('logger\\x20websocket\\x20error'));},_0x32a333[_0x27af0b(0x264)]=()=>{var _0x3f5ab4=_0x27af0b;this[_0x3f5ab4(0x271)]||_0x32a333['_socket']&&_0x32a333[_0x3f5ab4(0x1ce)][_0x3f5ab4(0x25e)]&&_0x32a333[_0x3f5ab4(0x1ce)][_0x3f5ab4(0x25e)](),_0x2bc56a(_0x32a333);},_0x32a333[_0x27af0b(0x209)]=()=>{var _0x45f624=_0x27af0b;this[_0x45f624(0x1dd)]=!0x0,this[_0x45f624(0x298)](_0x32a333),this[_0x45f624(0x258)]();},_0x32a333[_0x27af0b(0x1fa)]=_0x176016=>{var _0x6a695e=_0x27af0b;try{if(!(_0x176016!=null&&_0x176016[_0x6a695e(0x235)])||!this[_0x6a695e(0x29e)])return;let _0x1709d9=JSON[_0x6a695e(0x283)](_0x176016[_0x6a695e(0x235)]);this['eventReceivedCallback'](_0x1709d9['method'],_0x1709d9[_0x6a695e(0x265)],this[_0x6a695e(0x274)],this[_0x6a695e(0x271)]);}catch{}};})['then'](_0xbbe96=>(this['_connected']=!0x0,this['_connecting']=!0x1,this['_allowedToConnectOnSend']=!0x1,this[_0xaba3e1(0x24a)]=!0x0,this[_0xaba3e1(0x255)]=0x0,_0xbbe96))['catch'](_0x2b00a7=>(this[_0xaba3e1(0x23d)]=!0x1,this[_0xaba3e1(0x2ae)]=!0x1,console['warn'](_0xaba3e1(0x214)+this[_0xaba3e1(0x236)]),_0x47d47f(new Error(_0xaba3e1(0x281)+(_0x2b00a7&&_0x2b00a7['message'])))));}));}[_0x578e2a(0x298)](_0x56096f){var _0x5ea0dd=_0x578e2a;this['_connected']=!0x1,this['_connecting']=!0x1;try{_0x56096f[_0x5ea0dd(0x209)]=null,_0x56096f[_0x5ea0dd(0x2ac)]=null,_0x56096f[_0x5ea0dd(0x264)]=null;}catch{}try{_0x56096f[_0x5ea0dd(0x245)]<0x2&&_0x56096f['close']();}catch{}}[_0x578e2a(0x258)](){var _0x4c1912=_0x578e2a;clearTimeout(this[_0x4c1912(0x1d9)]),!(this[_0x4c1912(0x255)]>=this[_0x4c1912(0x1d3)])&&(this[_0x4c1912(0x1d9)]=setTimeout(()=>{var _0x29bf5a=_0x4c1912,_0x1a3dd8;this['_connected']||this[_0x29bf5a(0x2ae)]||(this[_0x29bf5a(0x20a)](),(_0x1a3dd8=this[_0x29bf5a(0x27e)])==null||_0x1a3dd8[_0x29bf5a(0x2ad)](()=>this[_0x29bf5a(0x258)]()));},0x1f4),this[_0x4c1912(0x1d9)][_0x4c1912(0x25e)]&&this['_reconnectTimeout'][_0x4c1912(0x25e)]());}async['send'](_0x18d513){var _0x5d94af=_0x578e2a;try{if(!this[_0x5d94af(0x24a)])return;this['_allowedToConnectOnSend']&&this[_0x5d94af(0x20a)](),(await this['_ws'])[_0x5d94af(0x247)](JSON['stringify'](_0x18d513));}catch(_0xbed769){console[_0x5d94af(0x29b)](this[_0x5d94af(0x234)]+':\\x20'+(_0xbed769&&_0xbed769[_0x5d94af(0x1c6)])),this[_0x5d94af(0x24a)]=!0x1,this[_0x5d94af(0x258)]();}}};function q(_0x3065a1,_0x269f51,_0x2dde02,_0x260765,_0x41b844,_0x2789ef,_0x2583ae,_0x5e7bd7=ie){var _0x2553b9=_0x578e2a;let _0x285def=_0x2dde02[_0x2553b9(0x223)](',')['map'](_0x2b28f0=>{var _0x125bd5=_0x2553b9,_0x9f8c86,_0x1e871f,_0x5922d9,_0x47c6e7;try{if(!_0x3065a1[_0x125bd5(0x21a)]){let _0x24b436=((_0x1e871f=(_0x9f8c86=_0x3065a1[_0x125bd5(0x21c)])==null?void 0x0:_0x9f8c86[_0x125bd5(0x287)])==null?void 0x0:_0x1e871f['node'])||((_0x47c6e7=(_0x5922d9=_0x3065a1[_0x125bd5(0x21c)])==null?void 0x0:_0x5922d9[_0x125bd5(0x22a)])==null?void 0x0:_0x47c6e7[_0x125bd5(0x2a1)])==='edge';(_0x41b844===_0x125bd5(0x1f7)||_0x41b844==='remix'||_0x41b844===_0x125bd5(0x1fb)||_0x41b844==='angular')&&(_0x41b844+=_0x24b436?_0x125bd5(0x2b3):_0x125bd5(0x2a7)),_0x3065a1['_console_ninja_session']={'id':+new Date(),'tool':_0x41b844},_0x2583ae&&_0x41b844&&!_0x24b436&&console[_0x125bd5(0x26f)](_0x125bd5(0x241)+(_0x41b844[_0x125bd5(0x294)](0x0)[_0x125bd5(0x238)]()+_0x41b844[_0x125bd5(0x233)](0x1))+',',_0x125bd5(0x250),_0x125bd5(0x1ca));}let _0x355bda=new x(_0x3065a1,_0x269f51,_0x2b28f0,_0x260765,_0x2789ef,_0x5e7bd7);return _0x355bda[_0x125bd5(0x247)][_0x125bd5(0x1f1)](_0x355bda);}catch(_0x257eed){return console['warn'](_0x125bd5(0x212),_0x257eed&&_0x257eed[_0x125bd5(0x1c6)]),()=>{};}});return _0x80f31b=>_0x285def[_0x2553b9(0x2af)](_0x42e048=>_0x42e048(_0x80f31b));}function ie(_0x2801d9,_0x14e132,_0x5b5fa8,_0x2dd967){_0x2dd967&&_0x2801d9==='reload'&&_0x5b5fa8['location']['reload']();}function _0x1eb0(_0x1885ed,_0x553f30){var _0x345fd0=_0x345f();return _0x1eb0=function(_0x1eb0e2,_0x12a97e){_0x1eb0e2=_0x1eb0e2-0x1c4;var _0x122aa9=_0x345fd0[_0x1eb0e2];return _0x122aa9;},_0x1eb0(_0x1885ed,_0x553f30);}function b(_0xc6a9a3){var _0x4373fa=_0x578e2a,_0x3d4a81,_0x223bad;let _0x285e16=function(_0x58dee3,_0x1a47e6){return _0x1a47e6-_0x58dee3;},_0x290e05;if(_0xc6a9a3[_0x4373fa(0x273)])_0x290e05=function(){return _0xc6a9a3['performance']['now']();};else{if(_0xc6a9a3[_0x4373fa(0x21c)]&&_0xc6a9a3['process'][_0x4373fa(0x263)]&&((_0x223bad=(_0x3d4a81=_0xc6a9a3[_0x4373fa(0x21c)])==null?void 0x0:_0x3d4a81[_0x4373fa(0x22a)])==null?void 0x0:_0x223bad[_0x4373fa(0x2a1)])!==_0x4373fa(0x1e5))_0x290e05=function(){var _0x30097f=_0x4373fa;return _0xc6a9a3[_0x30097f(0x21c)][_0x30097f(0x263)]();},_0x285e16=function(_0x451b6d,_0x1be724){return 0x3e8*(_0x1be724[0x0]-_0x451b6d[0x0])+(_0x1be724[0x1]-_0x451b6d[0x1])/0xf4240;};else try{let {performance:_0x4c7b19}=require(_0x4373fa(0x1e7));_0x290e05=function(){var _0x32dd35=_0x4373fa;return _0x4c7b19[_0x32dd35(0x27a)]();};}catch{_0x290e05=function(){return+new Date();};}}return{'elapsed':_0x285e16,'timeStamp':_0x290e05,'now':()=>Date['now']()};}function X(_0x9caebe,_0x1879f2,_0xf159fc){var _0x6f66b9=_0x578e2a,_0x157092,_0x4db7ca,_0x5925dd,_0x2d8caa,_0x3acfb9;if(_0x9caebe[_0x6f66b9(0x28b)]!==void 0x0)return _0x9caebe[_0x6f66b9(0x28b)];let _0x4e3f85=((_0x4db7ca=(_0x157092=_0x9caebe[_0x6f66b9(0x21c)])==null?void 0x0:_0x157092[_0x6f66b9(0x287)])==null?void 0x0:_0x4db7ca[_0x6f66b9(0x24d)])||((_0x2d8caa=(_0x5925dd=_0x9caebe['process'])==null?void 0x0:_0x5925dd[_0x6f66b9(0x22a)])==null?void 0x0:_0x2d8caa['NEXT_RUNTIME'])==='edge';return _0x4e3f85&&_0xf159fc===_0x6f66b9(0x1db)?_0x9caebe['_consoleNinjaAllowedToStart']=!0x1:_0x9caebe[_0x6f66b9(0x28b)]=_0x4e3f85||!_0x1879f2||((_0x3acfb9=_0x9caebe[_0x6f66b9(0x24c)])==null?void 0x0:_0x3acfb9[_0x6f66b9(0x237)])&&_0x1879f2[_0x6f66b9(0x290)](_0x9caebe[_0x6f66b9(0x24c)][_0x6f66b9(0x237)]),_0x9caebe[_0x6f66b9(0x28b)];}function H(_0x2d6544,_0x31042d,_0x23472b,_0x52c704){var _0x5bfe86=_0x578e2a;_0x2d6544=_0x2d6544,_0x31042d=_0x31042d,_0x23472b=_0x23472b,_0x52c704=_0x52c704;let _0x498533=b(_0x2d6544),_0x1240bf=_0x498533['elapsed'],_0x1d3aa8=_0x498533[_0x5bfe86(0x2a0)];class _0x365c3f{constructor(){var _0x53f077=_0x5bfe86;this[_0x53f077(0x1d0)]=/^(?!(?:do|if|in|for|let|new|try|var|case|else|enum|eval|false|null|this|true|void|with|break|catch|class|const|super|throw|while|yield|delete|export|import|public|return|static|switch|typeof|default|extends|finally|package|private|continue|debugger|function|arguments|interface|protected|implements|instanceof)$)[_$a-zA-Z\\xA0-\\uFFFF][_$a-zA-Z0-9\\xA0-\\uFFFF]*$/,this['_numberRegExp']=/^(0|[1-9][0-9]*)$/,this[_0x53f077(0x282)]=/'([^\\\\']|\\\\')*'/,this[_0x53f077(0x2a9)]=_0x2d6544[_0x53f077(0x262)],this[_0x53f077(0x268)]=_0x2d6544[_0x53f077(0x279)],this['_getOwnPropertyDescriptor']=Object[_0x53f077(0x1e8)],this[_0x53f077(0x260)]=Object[_0x53f077(0x219)],this[_0x53f077(0x22f)]=_0x2d6544[_0x53f077(0x1f6)],this['_regExpToString']=RegExp['prototype'][_0x53f077(0x224)],this[_0x53f077(0x240)]=Date[_0x53f077(0x1c4)][_0x53f077(0x224)];}['serialize'](_0x7340a,_0x2e8be4,_0x327052,_0x46a6ff){var _0x448458=_0x5bfe86,_0x160b0a=this,_0x2634a2=_0x327052[_0x448458(0x25b)];function _0x499464(_0x113c78,_0x5451c1,_0x5778b3){var _0x48a84f=_0x448458;_0x5451c1['type']=_0x48a84f(0x22b),_0x5451c1[_0x48a84f(0x286)]=_0x113c78[_0x48a84f(0x1c6)],_0x31e1e8=_0x5778b3['node'][_0x48a84f(0x296)],_0x5778b3[_0x48a84f(0x24d)][_0x48a84f(0x296)]=_0x5451c1,_0x160b0a['_treeNodePropertiesBeforeFullValue'](_0x5451c1,_0x5778b3);}try{_0x327052['level']++,_0x327052['autoExpand']&&_0x327052['autoExpandPreviousObjects'][_0x448458(0x1cc)](_0x2e8be4);var _0x40b033,_0x329ffb,_0x3aab41,_0x34da2c,_0x2aa7b0=[],_0x94df9f=[],_0x1b0221,_0xcb43dc=this[_0x448458(0x292)](_0x2e8be4),_0x5bad83=_0xcb43dc==='array',_0x166be6=!0x1,_0x103ee3=_0xcb43dc===_0x448458(0x213),_0xa19b66=this[_0x448458(0x239)](_0xcb43dc),_0x13615e=this[_0x448458(0x1d4)](_0xcb43dc),_0x3ad163=_0xa19b66||_0x13615e,_0x2ac12d={},_0x221533=0x0,_0x5366a2=!0x1,_0x31e1e8,_0x23feec=/^(([1-9]{1}[0-9]*)|0)$/;if(_0x327052[_0x448458(0x295)]){if(_0x5bad83){if(_0x329ffb=_0x2e8be4[_0x448458(0x229)],_0x329ffb>_0x327052[_0x448458(0x2a3)]){for(_0x3aab41=0x0,_0x34da2c=_0x327052[_0x448458(0x2a3)],_0x40b033=_0x3aab41;_0x40b033<_0x34da2c;_0x40b033++)_0x94df9f[_0x448458(0x1cc)](_0x160b0a['_addProperty'](_0x2aa7b0,_0x2e8be4,_0xcb43dc,_0x40b033,_0x327052));_0x7340a[_0x448458(0x276)]=!0x0;}else{for(_0x3aab41=0x0,_0x34da2c=_0x329ffb,_0x40b033=_0x3aab41;_0x40b033<_0x34da2c;_0x40b033++)_0x94df9f[_0x448458(0x1cc)](_0x160b0a[_0x448458(0x243)](_0x2aa7b0,_0x2e8be4,_0xcb43dc,_0x40b033,_0x327052));}_0x327052['autoExpandPropertyCount']+=_0x94df9f[_0x448458(0x229)];}if(!(_0xcb43dc===_0x448458(0x284)||_0xcb43dc===_0x448458(0x262))&&!_0xa19b66&&_0xcb43dc!=='String'&&_0xcb43dc!==_0x448458(0x26c)&&_0xcb43dc!==_0x448458(0x1e3)){var _0x40db64=_0x46a6ff[_0x448458(0x1d1)]||_0x327052[_0x448458(0x1d1)];if(this[_0x448458(0x28f)](_0x2e8be4)?(_0x40b033=0x0,_0x2e8be4[_0x448458(0x2af)](function(_0x303a5b){var _0xc13ec4=_0x448458;if(_0x221533++,_0x327052[_0xc13ec4(0x23b)]++,_0x221533>_0x40db64){_0x5366a2=!0x0;return;}if(!_0x327052['isExpressionToEvaluate']&&_0x327052['autoExpand']&&_0x327052[_0xc13ec4(0x23b)]>_0x327052[_0xc13ec4(0x221)]){_0x5366a2=!0x0;return;}_0x94df9f[_0xc13ec4(0x1cc)](_0x160b0a[_0xc13ec4(0x243)](_0x2aa7b0,_0x2e8be4,_0xc13ec4(0x1d5),_0x40b033++,_0x327052,function(_0x141fa8){return function(){return _0x141fa8;};}(_0x303a5b)));})):this[_0x448458(0x215)](_0x2e8be4)&&_0x2e8be4[_0x448458(0x2af)](function(_0x3bc90c,_0x1f2dc2){var _0x1b3bdd=_0x448458;if(_0x221533++,_0x327052['autoExpandPropertyCount']++,_0x221533>_0x40db64){_0x5366a2=!0x0;return;}if(!_0x327052[_0x1b3bdd(0x1c5)]&&_0x327052[_0x1b3bdd(0x25b)]&&_0x327052[_0x1b3bdd(0x23b)]>_0x327052['autoExpandLimit']){_0x5366a2=!0x0;return;}var _0x4e8a3a=_0x1f2dc2['toString']();_0x4e8a3a[_0x1b3bdd(0x229)]>0x64&&(_0x4e8a3a=_0x4e8a3a[_0x1b3bdd(0x226)](0x0,0x64)+_0x1b3bdd(0x1f5)),_0x94df9f['push'](_0x160b0a[_0x1b3bdd(0x243)](_0x2aa7b0,_0x2e8be4,_0x1b3bdd(0x1e0),_0x4e8a3a,_0x327052,function(_0x3ba18d){return function(){return _0x3ba18d;};}(_0x3bc90c)));}),!_0x166be6){try{for(_0x1b0221 in _0x2e8be4)if(!(_0x5bad83&&_0x23feec[_0x448458(0x1f4)](_0x1b0221))&&!this['_blacklistedProperty'](_0x2e8be4,_0x1b0221,_0x327052)){if(_0x221533++,_0x327052[_0x448458(0x23b)]++,_0x221533>_0x40db64){_0x5366a2=!0x0;break;}if(!_0x327052[_0x448458(0x1c5)]&&_0x327052[_0x448458(0x25b)]&&_0x327052[_0x448458(0x23b)]>_0x327052['autoExpandLimit']){_0x5366a2=!0x0;break;}_0x94df9f[_0x448458(0x1cc)](_0x160b0a[_0x448458(0x20c)](_0x2aa7b0,_0x2ac12d,_0x2e8be4,_0xcb43dc,_0x1b0221,_0x327052));}}catch{}if(_0x2ac12d[_0x448458(0x21f)]=!0x0,_0x103ee3&&(_0x2ac12d[_0x448458(0x23c)]=!0x0),!_0x5366a2){var _0x4e554c=[][_0x448458(0x25a)](this['_getOwnPropertyNames'](_0x2e8be4))[_0x448458(0x25a)](this['_getOwnPropertySymbols'](_0x2e8be4));for(_0x40b033=0x0,_0x329ffb=_0x4e554c[_0x448458(0x229)];_0x40b033<_0x329ffb;_0x40b033++)if(_0x1b0221=_0x4e554c[_0x40b033],!(_0x5bad83&&_0x23feec['test'](_0x1b0221[_0x448458(0x224)]()))&&!this[_0x448458(0x1ef)](_0x2e8be4,_0x1b0221,_0x327052)&&!_0x2ac12d[_0x448458(0x1c8)+_0x1b0221['toString']()]){if(_0x221533++,_0x327052[_0x448458(0x23b)]++,_0x221533>_0x40db64){_0x5366a2=!0x0;break;}if(!_0x327052[_0x448458(0x1c5)]&&_0x327052['autoExpand']&&_0x327052[_0x448458(0x23b)]>_0x327052[_0x448458(0x221)]){_0x5366a2=!0x0;break;}_0x94df9f[_0x448458(0x1cc)](_0x160b0a['_addObjectProperty'](_0x2aa7b0,_0x2ac12d,_0x2e8be4,_0xcb43dc,_0x1b0221,_0x327052));}}}}}if(_0x7340a[_0x448458(0x285)]=_0xcb43dc,_0x3ad163?(_0x7340a[_0x448458(0x1ed)]=_0x2e8be4[_0x448458(0x23a)](),this[_0x448458(0x27f)](_0xcb43dc,_0x7340a,_0x327052,_0x46a6ff)):_0xcb43dc==='date'?_0x7340a['value']=this[_0x448458(0x240)][_0x448458(0x222)](_0x2e8be4):_0xcb43dc===_0x448458(0x1e3)?_0x7340a[_0x448458(0x1ed)]=_0x2e8be4[_0x448458(0x224)]():_0xcb43dc===_0x448458(0x256)?_0x7340a[_0x448458(0x1ed)]=this['_regExpToString']['call'](_0x2e8be4):_0xcb43dc===_0x448458(0x272)&&this[_0x448458(0x22f)]?_0x7340a[_0x448458(0x1ed)]=this[_0x448458(0x22f)]['prototype'][_0x448458(0x224)][_0x448458(0x222)](_0x2e8be4):!_0x327052[_0x448458(0x295)]&&!(_0xcb43dc===_0x448458(0x284)||_0xcb43dc===_0x448458(0x262))&&(delete _0x7340a['value'],_0x7340a[_0x448458(0x201)]=!0x0),_0x5366a2&&(_0x7340a['cappedProps']=!0x0),_0x31e1e8=_0x327052[_0x448458(0x24d)]['current'],_0x327052[_0x448458(0x24d)][_0x448458(0x296)]=_0x7340a,this['_treeNodePropertiesBeforeFullValue'](_0x7340a,_0x327052),_0x94df9f['length']){for(_0x40b033=0x0,_0x329ffb=_0x94df9f[_0x448458(0x229)];_0x40b033<_0x329ffb;_0x40b033++)_0x94df9f[_0x40b033](_0x40b033);}_0x2aa7b0['length']&&(_0x7340a[_0x448458(0x1d1)]=_0x2aa7b0);}catch(_0xd7cd3e){_0x499464(_0xd7cd3e,_0x7340a,_0x327052);}return this[_0x448458(0x26b)](_0x2e8be4,_0x7340a),this[_0x448458(0x1c7)](_0x7340a,_0x327052),_0x327052[_0x448458(0x24d)]['current']=_0x31e1e8,_0x327052[_0x448458(0x251)]--,_0x327052[_0x448458(0x25b)]=_0x2634a2,_0x327052[_0x448458(0x25b)]&&_0x327052[_0x448458(0x25f)][_0x448458(0x24f)](),_0x7340a;}['_getOwnPropertySymbols'](_0x1fae1c){var _0x169a39=_0x5bfe86;return Object[_0x169a39(0x28e)]?Object[_0x169a39(0x28e)](_0x1fae1c):[];}[_0x5bfe86(0x28f)](_0x382139){var _0x252123=_0x5bfe86;return!!(_0x382139&&_0x2d6544['Set']&&this[_0x252123(0x257)](_0x382139)===_0x252123(0x1cd)&&_0x382139[_0x252123(0x2af)]);}['_blacklistedProperty'](_0x50a8ea,_0x375822,_0x9cbb0b){var _0x280600=_0x5bfe86;return _0x9cbb0b[_0x280600(0x1cb)]?typeof _0x50a8ea[_0x375822]==_0x280600(0x213):!0x1;}[_0x5bfe86(0x292)](_0x134de8){var _0x3c325b=_0x5bfe86,_0xbfb60f='';return _0xbfb60f=typeof _0x134de8,_0xbfb60f==='object'?this[_0x3c325b(0x257)](_0x134de8)===_0x3c325b(0x1c9)?_0xbfb60f=_0x3c325b(0x2ab):this[_0x3c325b(0x257)](_0x134de8)==='[object\\x20Date]'?_0xbfb60f='date':this[_0x3c325b(0x257)](_0x134de8)===_0x3c325b(0x20b)?_0xbfb60f='bigint':_0x134de8===null?_0xbfb60f=_0x3c325b(0x284):_0x134de8[_0x3c325b(0x26e)]&&(_0xbfb60f=_0x134de8[_0x3c325b(0x26e)][_0x3c325b(0x278)]||_0xbfb60f):_0xbfb60f===_0x3c325b(0x262)&&this[_0x3c325b(0x268)]&&_0x134de8 instanceof this[_0x3c325b(0x268)]&&(_0xbfb60f=_0x3c325b(0x279)),_0xbfb60f;}['_objectToString'](_0xeb0f5b){var _0x316467=_0x5bfe86;return Object['prototype'][_0x316467(0x224)][_0x316467(0x222)](_0xeb0f5b);}[_0x5bfe86(0x239)](_0x3ffc68){var _0x49546e=_0x5bfe86;return _0x3ffc68===_0x49546e(0x29f)||_0x3ffc68===_0x49546e(0x1f8)||_0x3ffc68===_0x49546e(0x217);}[_0x5bfe86(0x1d4)](_0x1077d8){var _0x295ba1=_0x5bfe86;return _0x1077d8==='Boolean'||_0x1077d8===_0x295ba1(0x203)||_0x1077d8===_0x295ba1(0x26d);}[_0x5bfe86(0x243)](_0x4ac575,_0x125a96,_0x112f41,_0x4b555e,_0x56944c,_0x17836f){var _0x3dbfbc=this;return function(_0xc8ae20){var _0x17f82e=_0x1eb0,_0xa455bb=_0x56944c[_0x17f82e(0x24d)]['current'],_0x2a93e9=_0x56944c[_0x17f82e(0x24d)]['index'],_0x8969f7=_0x56944c[_0x17f82e(0x24d)][_0x17f82e(0x1cf)];_0x56944c['node'][_0x17f82e(0x1cf)]=_0xa455bb,_0x56944c[_0x17f82e(0x24d)][_0x17f82e(0x254)]=typeof _0x4b555e=='number'?_0x4b555e:_0xc8ae20,_0x4ac575[_0x17f82e(0x1cc)](_0x3dbfbc['_property'](_0x125a96,_0x112f41,_0x4b555e,_0x56944c,_0x17836f)),_0x56944c[_0x17f82e(0x24d)]['parent']=_0x8969f7,_0x56944c[_0x17f82e(0x24d)][_0x17f82e(0x254)]=_0x2a93e9;};}[_0x5bfe86(0x20c)](_0x22824c,_0x2c4de7,_0x1a348c,_0x593555,_0x5d7ee4,_0x3491d6,_0xcc32ec){var _0x5d620c=this;return _0x2c4de7['_p_'+_0x5d7ee4['toString']()]=!0x0,function(_0x31d7b6){var _0x1a80dc=_0x1eb0,_0xedb4f2=_0x3491d6[_0x1a80dc(0x24d)][_0x1a80dc(0x296)],_0x8a4f42=_0x3491d6[_0x1a80dc(0x24d)][_0x1a80dc(0x254)],_0x564a0c=_0x3491d6[_0x1a80dc(0x24d)][_0x1a80dc(0x1cf)];_0x3491d6[_0x1a80dc(0x24d)][_0x1a80dc(0x1cf)]=_0xedb4f2,_0x3491d6[_0x1a80dc(0x24d)][_0x1a80dc(0x254)]=_0x31d7b6,_0x22824c[_0x1a80dc(0x1cc)](_0x5d620c['_property'](_0x1a348c,_0x593555,_0x5d7ee4,_0x3491d6,_0xcc32ec)),_0x3491d6[_0x1a80dc(0x24d)]['parent']=_0x564a0c,_0x3491d6['node'][_0x1a80dc(0x254)]=_0x8a4f42;};}['_property'](_0x2780bf,_0x2bedbe,_0x1cfded,_0xf1f4f1,_0x454d6a){var _0x56039a=_0x5bfe86,_0x5c899d=this;_0x454d6a||(_0x454d6a=function(_0x494702,_0x41c159){return _0x494702[_0x41c159];});var _0x146801=_0x1cfded['toString'](),_0x138375=_0xf1f4f1['expressionsToEvaluate']||{},_0x106079=_0xf1f4f1['depth'],_0x36d23f=_0xf1f4f1['isExpressionToEvaluate'];try{var _0x2b5120=this[_0x56039a(0x215)](_0x2780bf),_0x1e959d=_0x146801;_0x2b5120&&_0x1e959d[0x0]==='\\x27'&&(_0x1e959d=_0x1e959d[_0x56039a(0x233)](0x1,_0x1e959d['length']-0x2));var _0x3fbae9=_0xf1f4f1['expressionsToEvaluate']=_0x138375[_0x56039a(0x1c8)+_0x1e959d];_0x3fbae9&&(_0xf1f4f1['depth']=_0xf1f4f1[_0x56039a(0x295)]+0x1),_0xf1f4f1[_0x56039a(0x1c5)]=!!_0x3fbae9;var _0x6a5596=typeof _0x1cfded==_0x56039a(0x272),_0x3dadeb={'name':_0x6a5596||_0x2b5120?_0x146801:this[_0x56039a(0x1ee)](_0x146801)};if(_0x6a5596&&(_0x3dadeb[_0x56039a(0x272)]=!0x0),!(_0x2bedbe===_0x56039a(0x2ab)||_0x2bedbe===_0x56039a(0x248))){var _0x4db49a=this[_0x56039a(0x299)](_0x2780bf,_0x1cfded);if(_0x4db49a&&(_0x4db49a[_0x56039a(0x1d2)]&&(_0x3dadeb['setter']=!0x0),_0x4db49a[_0x56039a(0x2a5)]&&!_0x3fbae9&&!_0xf1f4f1[_0x56039a(0x27b)]))return _0x3dadeb['getter']=!0x0,this[_0x56039a(0x225)](_0x3dadeb,_0xf1f4f1),_0x3dadeb;}var _0x1fa18e;try{_0x1fa18e=_0x454d6a(_0x2780bf,_0x1cfded);}catch(_0x67fc0e){return _0x3dadeb={'name':_0x146801,'type':_0x56039a(0x22b),'error':_0x67fc0e['message']},this[_0x56039a(0x225)](_0x3dadeb,_0xf1f4f1),_0x3dadeb;}var _0x20a543=this['_type'](_0x1fa18e),_0xc5945f=this[_0x56039a(0x239)](_0x20a543);if(_0x3dadeb['type']=_0x20a543,_0xc5945f)this[_0x56039a(0x225)](_0x3dadeb,_0xf1f4f1,_0x1fa18e,function(){var _0x419c66=_0x56039a;_0x3dadeb['value']=_0x1fa18e[_0x419c66(0x23a)](),!_0x3fbae9&&_0x5c899d[_0x419c66(0x27f)](_0x20a543,_0x3dadeb,_0xf1f4f1,{});});else{var _0xfeb1fe=_0xf1f4f1['autoExpand']&&_0xf1f4f1[_0x56039a(0x251)]<_0xf1f4f1[_0x56039a(0x21b)]&&_0xf1f4f1[_0x56039a(0x25f)][_0x56039a(0x1ea)](_0x1fa18e)<0x0&&_0x20a543!==_0x56039a(0x213)&&_0xf1f4f1[_0x56039a(0x23b)]<_0xf1f4f1[_0x56039a(0x221)];_0xfeb1fe||_0xf1f4f1[_0x56039a(0x251)]<_0x106079||_0x3fbae9?(this[_0x56039a(0x28c)](_0x3dadeb,_0x1fa18e,_0xf1f4f1,_0x3fbae9||{}),this[_0x56039a(0x26b)](_0x1fa18e,_0x3dadeb)):this['_processTreeNodeResult'](_0x3dadeb,_0xf1f4f1,_0x1fa18e,function(){var _0x519828=_0x56039a;_0x20a543===_0x519828(0x284)||_0x20a543===_0x519828(0x262)||(delete _0x3dadeb[_0x519828(0x1ed)],_0x3dadeb[_0x519828(0x201)]=!0x0);});}return _0x3dadeb;}finally{_0xf1f4f1[_0x56039a(0x29d)]=_0x138375,_0xf1f4f1['depth']=_0x106079,_0xf1f4f1[_0x56039a(0x1c5)]=_0x36d23f;}}[_0x5bfe86(0x27f)](_0x38d38c,_0x110038,_0x593d2d,_0x8fc325){var _0x5d50bc=_0x5bfe86,_0x348ec5=_0x8fc325[_0x5d50bc(0x26a)]||_0x593d2d[_0x5d50bc(0x26a)];if((_0x38d38c==='string'||_0x38d38c===_0x5d50bc(0x203))&&_0x110038[_0x5d50bc(0x1ed)]){let _0x36b631=_0x110038[_0x5d50bc(0x1ed)][_0x5d50bc(0x229)];_0x593d2d[_0x5d50bc(0x267)]+=_0x36b631,_0x593d2d[_0x5d50bc(0x267)]>_0x593d2d[_0x5d50bc(0x208)]?(_0x110038[_0x5d50bc(0x201)]='',delete _0x110038[_0x5d50bc(0x1ed)]):_0x36b631>_0x348ec5&&(_0x110038['capped']=_0x110038['value']['substr'](0x0,_0x348ec5),delete _0x110038[_0x5d50bc(0x1ed)]);}}[_0x5bfe86(0x215)](_0x3ee382){var _0x3765ac=_0x5bfe86;return!!(_0x3ee382&&_0x2d6544[_0x3765ac(0x1e0)]&&this[_0x3765ac(0x257)](_0x3ee382)===_0x3765ac(0x1e9)&&_0x3ee382[_0x3765ac(0x2af)]);}[_0x5bfe86(0x1ee)](_0x3f8395){var _0x399dcb=_0x5bfe86;if(_0x3f8395[_0x399dcb(0x25c)](/^\\d+$/))return _0x3f8395;var _0x315e4b;try{_0x315e4b=JSON[_0x399dcb(0x1da)](''+_0x3f8395);}catch{_0x315e4b='\\x22'+this[_0x399dcb(0x257)](_0x3f8395)+'\\x22';}return _0x315e4b['match'](/^\"([a-zA-Z_][a-zA-Z_0-9]*)\"$/)?_0x315e4b=_0x315e4b[_0x399dcb(0x233)](0x1,_0x315e4b[_0x399dcb(0x229)]-0x2):_0x315e4b=_0x315e4b[_0x399dcb(0x2a8)](/'/g,'\\x5c\\x27')['replace'](/\\\\\"/g,'\\x22')[_0x399dcb(0x2a8)](/(^\"|\"$)/g,'\\x27'),_0x315e4b;}[_0x5bfe86(0x225)](_0x3da7a0,_0x7ace53,_0x1e34a5,_0x5cb48b){var _0x126008=_0x5bfe86;this[_0x126008(0x1d6)](_0x3da7a0,_0x7ace53),_0x5cb48b&&_0x5cb48b(),this[_0x126008(0x26b)](_0x1e34a5,_0x3da7a0),this[_0x126008(0x1c7)](_0x3da7a0,_0x7ace53);}[_0x5bfe86(0x1d6)](_0x388b3a,_0x2eff80){var _0x14526d=_0x5bfe86;this[_0x14526d(0x23e)](_0x388b3a,_0x2eff80),this[_0x14526d(0x266)](_0x388b3a,_0x2eff80),this[_0x14526d(0x1e6)](_0x388b3a,_0x2eff80),this[_0x14526d(0x28a)](_0x388b3a,_0x2eff80);}[_0x5bfe86(0x23e)](_0x27af3a,_0x227161){}[_0x5bfe86(0x266)](_0x2bc9d0,_0x26af78){}['_setNodeLabel'](_0x430601,_0x28f708){}[_0x5bfe86(0x205)](_0x462abc){var _0xe4ffc3=_0x5bfe86;return _0x462abc===this[_0xe4ffc3(0x2a9)];}[_0x5bfe86(0x1c7)](_0x3ebaaf,_0x4ae2f6){var _0xf397a5=_0x5bfe86;this[_0xf397a5(0x259)](_0x3ebaaf,_0x4ae2f6),this['_setNodeExpandableState'](_0x3ebaaf),_0x4ae2f6[_0xf397a5(0x1ff)]&&this[_0xf397a5(0x1dc)](_0x3ebaaf),this[_0xf397a5(0x2b1)](_0x3ebaaf,_0x4ae2f6),this[_0xf397a5(0x22c)](_0x3ebaaf,_0x4ae2f6),this[_0xf397a5(0x22d)](_0x3ebaaf);}[_0x5bfe86(0x26b)](_0x5d1221,_0x2ebcf7){var _0x5c5e59=_0x5bfe86;let _0x3d6658;try{_0x2d6544[_0x5c5e59(0x2a4)]&&(_0x3d6658=_0x2d6544['console'][_0x5c5e59(0x286)],_0x2d6544[_0x5c5e59(0x2a4)][_0x5c5e59(0x286)]=function(){}),_0x5d1221&&typeof _0x5d1221[_0x5c5e59(0x229)]==_0x5c5e59(0x217)&&(_0x2ebcf7[_0x5c5e59(0x229)]=_0x5d1221['length']);}catch{}finally{_0x3d6658&&(_0x2d6544[_0x5c5e59(0x2a4)][_0x5c5e59(0x286)]=_0x3d6658);}if(_0x2ebcf7[_0x5c5e59(0x285)]===_0x5c5e59(0x217)||_0x2ebcf7[_0x5c5e59(0x285)]===_0x5c5e59(0x26d)){if(isNaN(_0x2ebcf7['value']))_0x2ebcf7[_0x5c5e59(0x27c)]=!0x0,delete _0x2ebcf7[_0x5c5e59(0x1ed)];else switch(_0x2ebcf7[_0x5c5e59(0x1ed)]){case Number[_0x5c5e59(0x269)]:_0x2ebcf7['positiveInfinity']=!0x0,delete _0x2ebcf7['value'];break;case Number[_0x5c5e59(0x1f9)]:_0x2ebcf7['negativeInfinity']=!0x0,delete _0x2ebcf7[_0x5c5e59(0x1ed)];break;case 0x0:this[_0x5c5e59(0x27d)](_0x2ebcf7[_0x5c5e59(0x1ed)])&&(_0x2ebcf7[_0x5c5e59(0x244)]=!0x0);break;}}else _0x2ebcf7[_0x5c5e59(0x285)]===_0x5c5e59(0x213)&&typeof _0x5d1221[_0x5c5e59(0x278)]==_0x5c5e59(0x1f8)&&_0x5d1221[_0x5c5e59(0x278)]&&_0x2ebcf7[_0x5c5e59(0x278)]&&_0x5d1221[_0x5c5e59(0x278)]!==_0x2ebcf7[_0x5c5e59(0x278)]&&(_0x2ebcf7[_0x5c5e59(0x21e)]=_0x5d1221[_0x5c5e59(0x278)]);}[_0x5bfe86(0x27d)](_0x5c44ab){var _0x47b21d=_0x5bfe86;return 0x1/_0x5c44ab===Number[_0x47b21d(0x1f9)];}[_0x5bfe86(0x1dc)](_0x2703b2){var _0xd712e4=_0x5bfe86;!_0x2703b2[_0xd712e4(0x1d1)]||!_0x2703b2[_0xd712e4(0x1d1)]['length']||_0x2703b2[_0xd712e4(0x285)]===_0xd712e4(0x2ab)||_0x2703b2[_0xd712e4(0x285)]==='Map'||_0x2703b2['type']===_0xd712e4(0x1d5)||_0x2703b2['props']['sort'](function(_0x1857de,_0x41d5cc){var _0x574c4d=_0xd712e4,_0x1e8dfc=_0x1857de[_0x574c4d(0x278)][_0x574c4d(0x1f3)](),_0x273904=_0x41d5cc[_0x574c4d(0x278)][_0x574c4d(0x1f3)]();return _0x1e8dfc<_0x273904?-0x1:_0x1e8dfc>_0x273904?0x1:0x0;});}[_0x5bfe86(0x2b1)](_0x11c24d,_0x2ceb53){var _0x390d09=_0x5bfe86;if(!(_0x2ceb53[_0x390d09(0x1cb)]||!_0x11c24d['props']||!_0x11c24d[_0x390d09(0x1d1)]['length'])){for(var _0x414d3d=[],_0x1d0bf1=[],_0xb7edab=0x0,_0x1aa8a2=_0x11c24d[_0x390d09(0x1d1)]['length'];_0xb7edab<_0x1aa8a2;_0xb7edab++){var _0xafea7=_0x11c24d[_0x390d09(0x1d1)][_0xb7edab];_0xafea7[_0x390d09(0x285)]===_0x390d09(0x213)?_0x414d3d[_0x390d09(0x1cc)](_0xafea7):_0x1d0bf1['push'](_0xafea7);}if(!(!_0x1d0bf1[_0x390d09(0x229)]||_0x414d3d[_0x390d09(0x229)]<=0x1)){_0x11c24d[_0x390d09(0x1d1)]=_0x1d0bf1;var _0x3ce7d6={'functionsNode':!0x0,'props':_0x414d3d};this[_0x390d09(0x23e)](_0x3ce7d6,_0x2ceb53),this[_0x390d09(0x259)](_0x3ce7d6,_0x2ceb53),this[_0x390d09(0x242)](_0x3ce7d6),this[_0x390d09(0x28a)](_0x3ce7d6,_0x2ceb53),_0x3ce7d6['id']+='\\x20f',_0x11c24d[_0x390d09(0x1d1)][_0x390d09(0x1f0)](_0x3ce7d6);}}}[_0x5bfe86(0x22c)](_0x5e739f,_0x45407a){}[_0x5bfe86(0x242)](_0x27bee1){}[_0x5bfe86(0x246)](_0x329770){var _0xe8ad6e=_0x5bfe86;return Array[_0xe8ad6e(0x20f)](_0x329770)||typeof _0x329770==_0xe8ad6e(0x2b0)&&this[_0xe8ad6e(0x257)](_0x329770)===_0xe8ad6e(0x1c9);}[_0x5bfe86(0x28a)](_0x787970,_0x2084de){}[_0x5bfe86(0x22d)](_0x3dff96){var _0x1a15e3=_0x5bfe86;delete _0x3dff96['_hasSymbolPropertyOnItsPath'],delete _0x3dff96[_0x1a15e3(0x232)],delete _0x3dff96['_hasMapOnItsPath'];}[_0x5bfe86(0x1e6)](_0x2d5682,_0x1c57f0){}}let _0x3ce7f4=new _0x365c3f(),_0x35a933={'props':0x64,'elements':0x64,'strLength':0x400*0x32,'totalStrLength':0x400*0x32,'autoExpandLimit':0x1388,'autoExpandMaxDepth':0xa},_0x51fbad={'props':0x5,'elements':0x5,'strLength':0x100,'totalStrLength':0x100*0x3,'autoExpandLimit':0x1e,'autoExpandMaxDepth':0x2};function _0x1c2993(_0x490cd9,_0x32710d,_0x31b88c,_0x29a7fd,_0x4ff3a8,_0x12f7f2){var _0x161159=_0x5bfe86;let _0x11cd3a,_0x6587df;try{_0x6587df=_0x1d3aa8(),_0x11cd3a=_0x23472b[_0x32710d],!_0x11cd3a||_0x6587df-_0x11cd3a['ts']>0x1f4&&_0x11cd3a[_0x161159(0x1d8)]&&_0x11cd3a[_0x161159(0x21d)]/_0x11cd3a['count']<0x64?(_0x23472b[_0x32710d]=_0x11cd3a={'count':0x0,'time':0x0,'ts':_0x6587df},_0x23472b[_0x161159(0x270)]={}):_0x6587df-_0x23472b[_0x161159(0x270)]['ts']>0x32&&_0x23472b['hits'][_0x161159(0x1d8)]&&_0x23472b['hits']['time']/_0x23472b[_0x161159(0x270)][_0x161159(0x1d8)]<0x64&&(_0x23472b['hits']={});let _0x3a6703=[],_0x32b84f=_0x11cd3a[_0x161159(0x280)]||_0x23472b[_0x161159(0x270)][_0x161159(0x280)]?_0x51fbad:_0x35a933,_0xb6451d=_0x290f86=>{var _0x23f6d0=_0x161159;let _0x4eb512={};return _0x4eb512[_0x23f6d0(0x1d1)]=_0x290f86[_0x23f6d0(0x1d1)],_0x4eb512[_0x23f6d0(0x2a3)]=_0x290f86['elements'],_0x4eb512[_0x23f6d0(0x26a)]=_0x290f86['strLength'],_0x4eb512['totalStrLength']=_0x290f86[_0x23f6d0(0x208)],_0x4eb512[_0x23f6d0(0x221)]=_0x290f86[_0x23f6d0(0x221)],_0x4eb512['autoExpandMaxDepth']=_0x290f86[_0x23f6d0(0x21b)],_0x4eb512[_0x23f6d0(0x1ff)]=!0x1,_0x4eb512[_0x23f6d0(0x1cb)]=!_0x31042d,_0x4eb512[_0x23f6d0(0x295)]=0x1,_0x4eb512['level']=0x0,_0x4eb512[_0x23f6d0(0x2a6)]=_0x23f6d0(0x275),_0x4eb512[_0x23f6d0(0x230)]=_0x23f6d0(0x1ec),_0x4eb512[_0x23f6d0(0x25b)]=!0x0,_0x4eb512[_0x23f6d0(0x25f)]=[],_0x4eb512[_0x23f6d0(0x23b)]=0x0,_0x4eb512[_0x23f6d0(0x27b)]=!0x0,_0x4eb512[_0x23f6d0(0x267)]=0x0,_0x4eb512['node']={'current':void 0x0,'parent':void 0x0,'index':0x0},_0x4eb512;};for(var _0x30089d=0x0;_0x30089d<_0x4ff3a8[_0x161159(0x229)];_0x30089d++)_0x3a6703[_0x161159(0x1cc)](_0x3ce7f4[_0x161159(0x28c)]({'timeNode':_0x490cd9===_0x161159(0x21d)||void 0x0},_0x4ff3a8[_0x30089d],_0xb6451d(_0x32b84f),{}));if(_0x490cd9===_0x161159(0x2b2)){let _0x216ae4=Error[_0x161159(0x253)];try{Error[_0x161159(0x253)]=0x1/0x0,_0x3a6703[_0x161159(0x1cc)](_0x3ce7f4['serialize']({'stackNode':!0x0},new Error()['stack'],_0xb6451d(_0x32b84f),{'strLength':0x1/0x0}));}finally{Error[_0x161159(0x253)]=_0x216ae4;}}return{'method':_0x161159(0x26f),'version':_0x52c704,'args':[{'ts':_0x31b88c,'session':_0x29a7fd,'args':_0x3a6703,'id':_0x32710d,'context':_0x12f7f2}]};}catch(_0x249385){return{'method':_0x161159(0x26f),'version':_0x52c704,'args':[{'ts':_0x31b88c,'session':_0x29a7fd,'args':[{'type':_0x161159(0x22b),'error':_0x249385&&_0x249385[_0x161159(0x1c6)]}],'id':_0x32710d,'context':_0x12f7f2}]};}finally{try{if(_0x11cd3a&&_0x6587df){let _0x2ea20d=_0x1d3aa8();_0x11cd3a[_0x161159(0x1d8)]++,_0x11cd3a[_0x161159(0x21d)]+=_0x1240bf(_0x6587df,_0x2ea20d),_0x11cd3a['ts']=_0x2ea20d,_0x23472b[_0x161159(0x270)]['count']++,_0x23472b[_0x161159(0x270)][_0x161159(0x21d)]+=_0x1240bf(_0x6587df,_0x2ea20d),_0x23472b[_0x161159(0x270)]['ts']=_0x2ea20d,(_0x11cd3a['count']>0x32||_0x11cd3a['time']>0x64)&&(_0x11cd3a[_0x161159(0x280)]=!0x0),(_0x23472b[_0x161159(0x270)][_0x161159(0x1d8)]>0x3e8||_0x23472b['hits']['time']>0x12c)&&(_0x23472b[_0x161159(0x270)][_0x161159(0x280)]=!0x0);}}catch{}}}return _0x1c2993;}function _0x345f(){var _0xf1e565=['...','Symbol','next.js','string','NEGATIVE_INFINITY','onmessage','astro','port','426136eFTZOj','gateway.docker.internal','sortProps','default','capped','then','String','join','_isUndefined','_WebSocketClass','Console\\x20Ninja\\x20failed\\x20to\\x20send\\x20logs,\\x20refreshing\\x20the\\x20page\\x20may\\x20help;\\x20also\\x20see\\x20','totalStrLength','onclose','_connectToHostNow','[object\\x20BigInt]','_addObjectProperty','dockerizedApp','Console\\x20Ninja\\x20failed\\x20to\\x20send\\x20logs,\\x20restarting\\x20the\\x20process\\x20may\\x20help;\\x20also\\x20see\\x20','isArray','_WebSocket','680710nxUyMs','logger\\x20failed\\x20to\\x20connect\\x20to\\x20host','function','logger\\x20failed\\x20to\\x20connect\\x20to\\x20host,\\x20see\\x20','_isMap','_console_ninja','number','enumerable','getOwnPropertyNames','_console_ninja_session','autoExpandMaxDepth','process','time','funcName','_p_length','_inNextEdge','autoExpandLimit','call','split','toString','_processTreeNodeResult','slice','disabledLog','9ZMsnwd','length','env','unknown','_addLoadNode','_cleanNode','232566KyYDEE','_Symbol','rootExpression','1718122384146','_hasSetOnItsPath','substr','_sendErrorMessage','data','_webSocketErrorDocsLink','hostname','toUpperCase','_isPrimitiveType','valueOf','autoExpandPropertyCount','_p_name','_connected','_setNodeId','1ZwhbXi','_dateToString','%c\\x20Console\\x20Ninja\\x20extension\\x20is\\x20connected\\x20to\\x20','_setNodeExpandableState','_addProperty','negativeZero','readyState','_isArray','send','Error','elapsed','_allowedToSend','host','location','node','failed\\x20to\\x20find\\x20and\\x20load\\x20WebSocket','pop','background:\\x20rgb(30,30,30);\\x20color:\\x20rgb(255,213,92)','level','34805','stackTraceLimit','index','_connectAttemptCount','RegExp','_objectToString','_attemptToReconnectShortly','_setNodeLabel','concat','autoExpand','match','origin','unref','autoExpandPreviousObjects','_getOwnPropertyNames','10zBaGdv','undefined','hrtime','onopen','args','_setNodeQueryPath','allStrLength','_HTMLAllCollection','POSITIVE_INFINITY','strLength','_additionalMetadata','Buffer','Number','constructor','log','hits','_inBrowser','symbol','performance','global','root_exp_id','cappedElements','1.0.0','name','HTMLAllCollection','now','resolveGetters','nan','_isNegativeZero','_ws','_capIfString','reduceLimits','failed\\x20to\\x20connect\\x20to\\x20host:\\x20','_quotedRegExp','parse','null','type','error','versions','ws://','path','_setNodePermissions','_consoleNinjaAllowedToStart','serialize',[\"localhost\",\"127.0.0.1\",\"example.cypress.io\",\"wagner-HP-250-G8-Notebook-PC\",\"192.168.1.26\",\"172.20.0.1\",\"172.23.0.1\",\"172.22.0.1\"],'getOwnPropertySymbols','_isSet','includes','getWebSocketClass','_type','hasOwnProperty','charAt','depth','current','4662yKEqZN','_disposeWebsocket','_getOwnPropertyDescriptor','1506900ZwsaeT','warn','4720vcNjOL','expressionsToEvaluate','eventReceivedCallback','boolean','timeStamp','NEXT_RUNTIME','3517794IgbPoO','elements','console','get','expId','\\x20browser','replace','_undefined','nodeModules','array','onerror','catch','_connecting','forEach','object','_addFunctionsNode','trace','\\x20server','prototype','isExpressionToEvaluate','message','_treeNodePropertiesAfterFullValue','_p_','[object\\x20Array]','see\\x20https://tinyurl.com/2vt8jxzw\\x20for\\x20more\\x20info.','noFunctions','push','[object\\x20Set]','_socket','parent','_keyStrRegExp','props','set','_maxConnectAttemptCount','_isPrimitiveWrapperType','Set','_treeNodePropertiesBeforeFullValue','','count','_reconnectTimeout','stringify','nuxt','_sortProps','_allowedToConnectOnSend','',\"/home/wagner/.vscode/extensions/wallabyjs.console-ninja-1.0.324/node_modules\",'Map','12koQaJu','getPrototypeOf','bigint','__es'+'Module','edge','_setNodeExpressionPath','perf_hooks','getOwnPropertyDescriptor','[object\\x20Map]','indexOf','2561009SClEPN','root_exp','value','_propertyName','_blacklistedProperty','unshift','bind','ws/index.js','toLowerCase','test'];_0x345f=function(){return _0xf1e565;};return _0x345f();}((_0x188d62,_0x583ca9,_0x4daaef,_0x403be0,_0x7546ed,_0x1e0f4a,_0x19ab3b,_0x4f5e3a,_0x134985,_0x31c96f,_0x24b6bc)=>{var _0xba1f0d=_0x578e2a;if(_0x188d62[_0xba1f0d(0x216)])return _0x188d62['_console_ninja'];if(!X(_0x188d62,_0x4f5e3a,_0x7546ed))return _0x188d62['_console_ninja']={'consoleLog':()=>{},'consoleTrace':()=>{},'consoleTime':()=>{},'consoleTimeEnd':()=>{},'autoLog':()=>{},'autoLogMany':()=>{},'autoTraceMany':()=>{},'coverage':()=>{},'autoTrace':()=>{},'autoTime':()=>{},'autoTimeEnd':()=>{}},_0x188d62[_0xba1f0d(0x216)];let _0x5c931a=b(_0x188d62),_0x51d854=_0x5c931a[_0xba1f0d(0x249)],_0x45e8c3=_0x5c931a[_0xba1f0d(0x2a0)],_0x30e7c0=_0x5c931a[_0xba1f0d(0x27a)],_0x2e4195={'hits':{},'ts':{}},_0x2668e2=H(_0x188d62,_0x134985,_0x2e4195,_0x1e0f4a),_0x307792=_0xd04593=>{_0x2e4195['ts'][_0xd04593]=_0x45e8c3();},_0x2973b2=(_0x135778,_0x16b446)=>{let _0x5c5cbc=_0x2e4195['ts'][_0x16b446];if(delete _0x2e4195['ts'][_0x16b446],_0x5c5cbc){let _0x151baf=_0x51d854(_0x5c5cbc,_0x45e8c3());_0x3487b9(_0x2668e2('time',_0x135778,_0x30e7c0(),_0x18fea1,[_0x151baf],_0x16b446));}},_0x5241ef=_0xdf16d7=>{var _0x3b5147=_0xba1f0d,_0x29d373;return _0x7546ed===_0x3b5147(0x1f7)&&_0x188d62[_0x3b5147(0x25d)]&&((_0x29d373=_0xdf16d7==null?void 0x0:_0xdf16d7['args'])==null?void 0x0:_0x29d373[_0x3b5147(0x229)])&&(_0xdf16d7[_0x3b5147(0x265)][0x0][_0x3b5147(0x25d)]=_0x188d62[_0x3b5147(0x25d)]),_0xdf16d7;};_0x188d62[_0xba1f0d(0x216)]={'consoleLog':(_0x4900c,_0x1e84f4)=>{var _0x43f9cd=_0xba1f0d;_0x188d62[_0x43f9cd(0x2a4)][_0x43f9cd(0x26f)][_0x43f9cd(0x278)]!==_0x43f9cd(0x227)&&_0x3487b9(_0x2668e2(_0x43f9cd(0x26f),_0x4900c,_0x30e7c0(),_0x18fea1,_0x1e84f4));},'consoleTrace':(_0x4a2fe8,_0x4ca5d1)=>{var _0x13a1e8=_0xba1f0d;_0x188d62[_0x13a1e8(0x2a4)][_0x13a1e8(0x26f)][_0x13a1e8(0x278)]!=='disabledTrace'&&_0x3487b9(_0x5241ef(_0x2668e2(_0x13a1e8(0x2b2),_0x4a2fe8,_0x30e7c0(),_0x18fea1,_0x4ca5d1)));},'consoleTime':_0x4f4199=>{_0x307792(_0x4f4199);},'consoleTimeEnd':(_0x1fee29,_0x36d028)=>{_0x2973b2(_0x36d028,_0x1fee29);},'autoLog':(_0xde27ec,_0x4de85e)=>{_0x3487b9(_0x2668e2('log',_0x4de85e,_0x30e7c0(),_0x18fea1,[_0xde27ec]));},'autoLogMany':(_0x1c3294,_0x291fea)=>{var _0x2e6791=_0xba1f0d;_0x3487b9(_0x2668e2(_0x2e6791(0x26f),_0x1c3294,_0x30e7c0(),_0x18fea1,_0x291fea));},'autoTrace':(_0x38fd83,_0x489817)=>{var _0x1cd2cf=_0xba1f0d;_0x3487b9(_0x5241ef(_0x2668e2(_0x1cd2cf(0x2b2),_0x489817,_0x30e7c0(),_0x18fea1,[_0x38fd83])));},'autoTraceMany':(_0x4aa1ce,_0x2366ba)=>{var _0x4f9a03=_0xba1f0d;_0x3487b9(_0x5241ef(_0x2668e2(_0x4f9a03(0x2b2),_0x4aa1ce,_0x30e7c0(),_0x18fea1,_0x2366ba)));},'autoTime':(_0x5aa46a,_0x54da06,_0x33a2f0)=>{_0x307792(_0x33a2f0);},'autoTimeEnd':(_0x2eb72f,_0x5d44c8,_0x1e616b)=>{_0x2973b2(_0x5d44c8,_0x1e616b);},'coverage':_0x1d2f41=>{_0x3487b9({'method':'coverage','version':_0x1e0f4a,'args':[{'id':_0x1d2f41}]});}};let _0x3487b9=q(_0x188d62,_0x583ca9,_0x4daaef,_0x403be0,_0x7546ed,_0x31c96f,_0x24b6bc),_0x18fea1=_0x188d62[_0xba1f0d(0x21a)];return _0x188d62[_0xba1f0d(0x216)];})(globalThis,'127.0.0.1',_0x578e2a(0x252),_0x578e2a(0x1df),'next.js',_0x578e2a(0x277),_0x578e2a(0x231),_0x578e2a(0x28d),_0x578e2a(0x1d7),_0x578e2a(0x1de),'1');");}catch(e){}};/* istanbul ignore next */function oo_oo(i,...v){try{oo_cm().consoleLog(i, v);}catch(e){} return v};/* istanbul ignore next */function oo_tr(i,...v){try{oo_cm().consoleTrace(i, v);}catch(e){} return v};/* istanbul ignore next */function oo_ts(v){try{oo_cm().consoleTime(v);}catch(e){} return v;};/* istanbul ignore next */function oo_te(v, i){try{oo_cm().consoleTimeEnd(v, i);}catch(e){} return v;};/*eslint unicorn/no-abusive-eslint-disable:,eslint-comments/disable-enable-pair:,eslint-comments/no-unlimited-disable:,eslint-comments/no-aggregating-enable:,eslint-comments/no-duplicate-disable:,eslint-comments/no-unused-disable:,eslint-comments/no-unused-enable:,*/