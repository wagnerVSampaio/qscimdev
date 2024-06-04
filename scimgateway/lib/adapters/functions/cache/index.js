const { DataCache } = require("./DataCache");
const { caches } = require("../../data/caches");
const { createCacheFetchFunction } = require("./fetchFunction");

function cache() {
  let cachesObj = {};

  caches.forEach((item) => {
    cachesObj[item.name] = new DataCache(
      async () => await createCacheFetchFunction(item),
      item.port,
      item.expires_in
    );
  });

  return cachesObj;
}

module.exports = { cache };
