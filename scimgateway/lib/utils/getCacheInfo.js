const dot = require("dot-object");

function getCacheValue(str) {
  const regex = /{{cache\.([a-zA-Z0-9._]+)}}/;
  const match = str.match(regex);
  return match ? match[1] : null;
}

function filterCaches(caches, port) {
  return Object.entries(caches).reduce((acc, [key, cache]) => {
    if (cache.port === port) {
      acc[key] = cache;
    }
    return acc;
  }, {});
}

async function getCacheInfo(originalObj, caches, port) {
  if (!originalObj || typeof originalObj !== "object") {
    return undefined;
    // throw new TypeError("originalObj must be a non-null object");
  }

  const filteredCaches = filterCaches(caches, port);
  const flatObj = dot.dot(originalObj); // Flatten the original object

  const keys = Object.keys(flatObj);
  const promises = keys.map(async (key) => {
    const value = flatObj[key];
    const cacheKey = getCacheValue(value?.toString());
    if (cacheKey !== null) {
      const [mainKey, ...pathParts] = cacheKey.split(".");
      const cache = filteredCaches[mainKey];
      if (cache) {
        try {
          const result = await cache.getData();
          if (result) {
            flatObj[key] = pathParts.reduce((acc, part) => acc?.[part], result);
          }
        } catch (error) {
          console.error(`Error fetching cache data for ${mainKey}:`, error);
        }
      }
    }
  });

  await Promise.all(promises);

  const updatedObj = dot.object(flatObj); // Reconstruct the original object
  return updatedObj;
}

module.exports = { getCacheInfo };
