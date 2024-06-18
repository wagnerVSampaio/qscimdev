const { Engine } = require("json-rules-engine");
const { getCacheInfo } = require("../../../utils/getCacheInfo");

async function createEngine(type, conditions, ctx, caches, port) {
  let engine = new Engine();

  let formattedConditions = [];

  let conditionsString = await Promise.all(
    conditions.map(async (cd) => {
      let formattedCd = await getCacheInfo(cd, caches, port);
      formattedConditions.push(formattedCd);
      return `${formattedCd.fact} ${formattedCd.operator} ${formattedCd.value}`;
    })
  );

  engine.addRule({
    conditions: {
      [type]: formattedConditions,
    },
    onSuccess() {
      return;
    },
    onFailure() {
      let errorBody = ctx?.body || [];
      ctx.body = {
        rules: [...errorBody, ...conditionsString],
      };
      throw new Error("verification failed");
    },
    event: {
      type: "message",
    },
  });

  return engine;
}

module.exports = { createEngine };
