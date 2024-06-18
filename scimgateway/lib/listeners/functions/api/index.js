const { formatAuth } = require("../../../utils/formatAuth");
const axios = require("axios");

async function useApiListener(config, auth, endpointMapper, map) {
  const filteredAuth = auth.basic.filter((item) => !item.readOnly)[0];

  if (!filteredAuth) {
    console.error("No Basic Auth provided for Rest API listener");
  }

  const token = Buffer.from(
    `${filteredAuth.username}:${filteredAuth.password}`
  ).toString("base64");

  // let formattedAuth = formatAuth(
  //   await getCacheInfo(config.auth, caches, port)
  // );

  // let headers = {
  //   Authorization: formattedAuth,
  //   ...(config.headers || {}),
  // };

  const api = axios.create({
    baseURL: `http://localhost:${config.port}/${config.path}`,
    headers: {
      Authorization: `Basic ${token}`,
    },
  });

  async function makeRequest() {
    try {
      const requestResponse = await axios
        .request({
          url: config.url,
          method: config.method,
          headers: {
            Authorization: formatAuth(config.auth),
            ...config.headers,
          },
          data: config.body,
        })
        .then((response) => response.data[config.dataField]);

      for (const item of requestResponse) {
        let data = {};

        if (config.mapping && Object.keys(config.mapping).length) {
          data = await endpointMapper("inbound", item, config.mapping).then(
            (res) => res[0]
          );
        }

        if (Object.keys(data).length) {
          let idValue = config.path === "users" ? data.userName : data.id;

          await api
            .get(`/${idValue}`)
            .then((res) => {
              console.log(`${config.path} Already exist!`);
              if (config.update) {
                console.log("Updating...");
                api.patch(`/${idValue}`, data);
              }
            })
            .catch((err) => {
              console.log(`${config.path} Already does not exist! Creating...`);
              api.post("", data);
            });
        } else {
          console.log(`Error creating ${config.path}: Empty payload`);
        }
      }
    } catch (err) {
      console.error(`Error while running API listener: ${err.message}`);

      if (config.on_error) {
        function executeScript(obj) {
          return eval?.(`"use strict";(${obj})`);
        }
        executeScript(config.on_error);
      }
    }
  }
  const intervalId = setInterval(makeRequest, config.time * 1000);
}

module.exports = { useApiListener };
