const { notifications } = require("./data/notifications");
const { slackMessages } = require("./data/slackMessages");

const { fetchNotification } = require("./functions/notifications");
const { sendSlackMessage } = require("./functions/slackMessages");

function verifyAllowedRequests(allowedRequests, method, path) {
  const results = allowedRequests.map(
    (item) => item.method === method && item.path === path
  );

  return results.some((item) => item === true);
}

async function fetchAdapters(ctx, type, caches, verifyTracing, scimData) {
  const port = ctx.request.header.host.split(":")[1];

  const adapters = [
    ...(notifications?.map((item) => ({
      ...item,
      adapterType: "notification",
    })) || []),
    ...(slackMessages?.map((item) => ({
      ...item,
      adapterType: "slackMessage",
    })) || []),
  ].filter(
    (item) =>
      item.port === port &&
      item.type === type &&
      verifyAllowedRequests(
        item.allowed_requests,
        ctx.request.method,
        ctx.request.url.split("/")[1].toLowerCase()
      )
  );

  for (const item of adapters) {
    try {
      let newSpan = verifyTracing(ctx, `fetch adapter - ${item.adapterType}`);

      switch (item.adapterType) {
        case "notification":
          await fetchNotification(ctx, item, caches, scimData);
          break;
        case "slackMessage":
          await sendSlackMessage(ctx, item, caches, scimData);
          break;
        default:
          break;
      }
      newSpan?.end();
    } catch (error) {
      console.error(`Error running adapter - ${item.adapterType}`);
      console.log(error);
    }
  }
  return true;
}

module.exports = { fetchAdapters };
