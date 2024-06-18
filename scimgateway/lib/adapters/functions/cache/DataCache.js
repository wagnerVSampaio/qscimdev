let api;
try {
  api = require("@opentelemetry/api");
} catch (err) {}

class DataCache {
  constructor(fetchFunction, port, minutesToLive = 10) {
    this.port = port;
    this.millisecondsToLive = minutesToLive * 60 * 1000;
    this.fetchFunction = fetchFunction;
    this.cache = null;
    this.getData = this.getData.bind(this);
    this.resetCache = this.resetCache.bind(this);
    this.isCacheExpired = this.isCacheExpired.bind(this);
    this.fetchDate = new Date(0);
  }
  isCacheExpired() {
    return (
      this.fetchDate.getTime() + this.millisecondsToLive < new Date().getTime()
    );
  }
  getData() {
    if (!this.cache || this.isCacheExpired()) {
      console.log("expired - fetching new data");
      return this.fetchFunction().then((data) => {
        this.cache = data;
        this.fetchDate = new Date();
        const activeSpan = api?.trace.getSpan(api?.context.active());
        activeSpan?.addEvent("Adapter: Getting cache info");
        return data;
      });
    } else {
      const activeSpan = api?.trace.getSpan(api?.context.active());
      activeSpan?.addEvent("Adapter: Recovering cache info");
      console.log("cache hit");
      return Promise.resolve(this.cache);
    }
  }
  resetCache() {
    this.fetchDate = new Date(0);
  }
}

module.exports = { DataCache };
