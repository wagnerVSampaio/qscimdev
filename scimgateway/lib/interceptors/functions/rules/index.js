const { createEngine } = require("./engine");
let api;
try {
  api = require("@opentelemetry/api");
} catch (err) {}

async function verifyRules(ctx, caches, rule) {
  const activeSpan = api?.trace.getSpan(api?.context.active());
  activeSpan?.addEvent("Interceptor: Verify business rule");

  const port = ctx.request.header.host.split(":")[1];
  let engine = await createEngine(
    rule.type,
    rule.conditions,
    ctx,
    caches,
    port
  );

  await engine.run(ctx.request.body);
}

module.exports = { verifyRules };
