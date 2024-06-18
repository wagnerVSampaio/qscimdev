const { getCacheInfo } = require("../../../utils/getCacheInfo");
const { WebClient } = require("@slack/web-api");

let api;
try {
  api = require("@opentelemetry/api");
} catch (err) {}

async function sendSlackMessage(ctx, item, caches, scimData) {
  const formattedItem = await getCacheInfo(item, caches, item.port);
  const web = new WebClient(formattedItem.token);

  const hasScimData = scimData && scimData.length;
  let formattedBody = hasScimData ? scimData[0] : ctx.request.body;

  if (ctx.request.url.split("/").length > 2) {
    formattedBody.userName =
      formattedBody?.userName || ctx.request.url.split("/").at(-1);
  }

  await web.chat
    .postMessage({
      channel: formattedItem.channel_id,
      username: `QSCIM Notifications - ${ctx.request.url
        .split("/")[1]
        .toLowerCase()} - ${item.type}`,
      // icon_emoji: ":robot_face:",
      text: `Notification: ${ctx.request.url.split("/")[1].toLowerCase()} - ${
        item.type
      }
     \`\`\` ${JSON.stringify(
       formattedItem.payload === "response" ? ctx.body : formattedBody,
       null,
       2
     )} \`\`\``,
    })
    .catch((err) => {
      activeSpan?.addEvent("Adapter: Error sending Slack message");
      throw new Error(err);
    });

  const activeSpan = api?.trace.getSpan(api?.context.active());
  activeSpan?.addEvent("Adapter: Sending Slack message");
}

module.exports = { sendSlackMessage };
