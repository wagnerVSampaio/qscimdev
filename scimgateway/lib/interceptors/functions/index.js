const { rules } = require("../data/rules");
const { requests } = require("../data/requests");

const { verifyRules } = require("./rules");
const { fetchApi } = require("./api");

function verifyAllowedRequests(allowedRequests, method, path) {
  const results = allowedRequests.map(
    (item) => item.method === method && item.path === path
  );

  return results.some((item) => item === true);
}

async function fetchInterceptors(ctx, caches, verifyTracing) {
  const port = ctx.request.header.host.split(":")[1];

  const interceptors = [
    ...(requests?.map((item) => ({ ...item, interceptorType: "request" })) ||
      []),
    ...(rules?.map((item) => ({ ...item, interceptorType: "rule" })) || []),
  ]
    .filter(
      (item) =>
        item.port === port &&
        verifyAllowedRequests(
          item.allowed_requests,
          ctx.request.method,
          ctx.request.url.split("/")[1].toLowerCase()
        )
    )
    .sort((a, b) => a.position - b.position);

  for (const item of interceptors) {
    try {
      let newSpan = verifyTracing(
        ctx,
        `fetch interceptors - ${item.interceptorType}`
      );

      switch (item.interceptorType) {
        case "request":
          await fetchApi(ctx, caches, item);
          break;
        case "rule":
          await verifyRules(ctx, caches, item);
          break;
        default:
          break;
      }
      newSpan?.end();
    } catch (error) {
      let errorMessage = error.message;
      switch (item.interceptorType) {
        case "request":
          errorMessage = `Request to ${item.url} failed`;
          break;
        case "rule":
          if (error.message !== "verification failed") {
            errorMessage = `Missing one of required fields: ${item.conditions.map(
              (cd) => cd.fact
            )}`;
          } else {
            errorMessage = `Verification failed for rules ${ctx.body?.rules}`;
          }
          break;
        default:
          break;
      }

      if (item.on_error) {
        function executeScript(obj) {
          return eval?.(`"use strict";(${obj})`);
        }
        executeScript(item.on_error);
      }

      if (item.block_on_error !== undefined ? item.block_on_error : true) {
        ctx.status = 400;
        ctx.body = {
          schemas: ["urn:ietf:params:scim:api:messages:2.0:Error"],
          detail: item.errorMessage || `Error while running interceptor(${item.interceptorType}): ${errorMessage}`,
          status: 400,
        };
        return false;
      }
    }
  }
  return true;
}

module.exports = { fetchInterceptors };
