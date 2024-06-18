const { formatAuth } = require("../../../utils/formatAuth");
const axios = require("axios");
let api;
try {
  api = require("@opentelemetry/api");
} catch (err) {}

async function createCacheFetchFunction(request) {
  const activeSpan = api?.trace.getSpan(api?.context.active());
  try {
    let headers = {
      Authorization: formatAuth(request.auth),
      ...request.headers,
    };

    activeSpan?.addEvent("Getting Cache");

    const response = await axios
      .request({
        url: request.url,
        method: request.method,
        headers,
        data: request.body,
      })
      .then((res) => res.data);

    let responseAttrs = {};
    request.mapping.forEach((item) => {
      responseAttrs[item.mapTo] = response[item.name];
    });

    return responseAttrs;
  } catch (error) {
    activeSpan?.addEvent("Adapter: Error sending notification");
    console.log("Error caching information:", error.message);
    return {};
  }
}

module.exports = { createCacheFetchFunction };
