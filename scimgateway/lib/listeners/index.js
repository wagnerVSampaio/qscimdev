const { apiListeners } = require("./data/api");
const { kafkaListeners } = require("./data/kafka");

const { useApiListener } = require("./functions/api");
const { useKafkaListener } = require("./functions/kafka");
const { getCacheInfo } = require("../utils/getCacheInfo");

async function useListeners(endpointMapper, auth, map, caches) {
  const listeners = [
    ...(apiListeners?.map((item) => ({ ...item, listenerType: "api" })) || []),
    ...(kafkaListeners?.map((item) => ({ ...item, listenerType: "kafka" })) ||
      []),
  ].sort((a, b) => a.position - b.position);

  for (const item of listeners) {
    const formattedItem = await getCacheInfo(item, caches, item.port);

    try {
      switch (item.listenerType) {
        case "api":
          await useApiListener(formattedItem, auth, endpointMapper, map);
          break;
        case "kafka":
          await useKafkaListener(formattedItem, auth, endpointMapper, map);
          break;
        default:
          break;
      }
    } catch (error) {
      console.log(`Error using listener ${item.listenerType}: ${error}`);

      if (item.on_error) {
        function executeScript(obj) {
          return eval?.(`"use strict";(${obj})`);
        }
        executeScript(item.on_error);
      }
    }
  }
}

module.exports = { useListeners };
