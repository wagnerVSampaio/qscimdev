const { formatAuth } = require("../../../utils/formatAuth");
const { formatURL } = require("../../../utils/formatURL");
const { getCacheInfo } = require("../../../utils/getCacheInfo");
let api;
try {
  api = require("@opentelemetry/api");
} catch (err) {}

async function fetchApi(ctx, caches, request) {
  const activeSpan = api?.trace.getSpan(api?.context.active());
  activeSpan?.addEvent("Interceptor: Fetch to API");

  const port = ctx.request.header.host.split(":")[1];
  let formattedURL = formatURL(ctx.request.body, request.url);

  let formattedAuth = formatAuth(
    await getCacheInfo(request.auth, caches, port)
  );

  let headers = {
    Authorization: formattedAuth,
    ...(request.headers || {}),
  };

  if (request.body) {
    headers["Content-Type"] = "application/json";
  }

  const response = await fetch(formattedURL, {
    method: request.method,
    headers: getCacheInfo(headers, caches, port),
    body: request.body
      ? JSON.stringify(getCacheInfo(request.body), caches, port)
      : undefined,
  });
  const jsonData = await response.json();

  let responseAttrs = {};
  request.mapping.forEach((item) => {
    responseAttrs[item.mapTo] = jsonData[item.name];
  });

  ctx.request.body = { ...ctx.request.body, ...responseAttrs };
}

module.exports = { fetchApi };
