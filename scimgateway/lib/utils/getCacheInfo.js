function getCacheValue(str) {
  const regex = /{{cache\.([a-zA-Z0-9._]+)}}/;
  const match = str.match(regex);
  return match ? match[1] : null;
}

function filterCaches(caches, port) {
  let filteredCaches = {};
  Object.keys(caches).forEach((key) => {
    if (caches[key].port === port) {
      filteredCaches[key] = caches[key];
    }
  });
  return filteredCaches;
}

async function getCacheInfo(originalObj, caches, port) {
  let filteredCaches = filterCaches(caches, port);

  for (const field in originalObj) {
    const value = getCacheValue(originalObj[field].toString());
    if (value !== null) {
      const splittedValue = value.split(".");
      const result = await filteredCaches[splittedValue[0]]?.getData();
      originalObj[field] = result[splittedValue.slice(1).join(".")];
    }
  }
  return originalObj;
}

module.exports = { getCacheInfo };
