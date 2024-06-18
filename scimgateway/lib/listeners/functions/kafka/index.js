const { Kafka } = require("kafkajs");
const axios = require("axios");

async function useKafkaListener(config, auth, endpointMapper, map) {
  const kafka = new Kafka({
    clientId: config.client_id,
    brokers: [config.url],
    sasl: {
      username: config.auth.username,
      password: config.auth.password,
      mechanism: config.auth.mechanism,
    },
    ssl: true,
  });

  const filteredAuth = auth.basic.filter((item) => !item.readOnly)[0];

  if (!filteredAuth) {
    console.error("No Basic Auth provided for kafka listener");
  }

  const token = Buffer.from(
    `${filteredAuth.username}:${filteredAuth.password}`
  ).toString("base64");
  const consumer = kafka.consumer({ groupId: config.group_id });

  const api = axios.create({
    baseURL: `http://localhost:${config.port}/${config.path}`,
    headers: {
      Authorization: `Basic ${token}`,
    },
  });

  async function handleMessages() {
    await consumer.connect();
    await consumer.subscribe({ topic: config.topic, fromBeginning: false });

    await consumer.run({
      eachMessage: async ({ topic, partition, message }) => {
        try {
          data = JSON.parse(message.value.toString());

          if (config.mapping && Object.keys(config.mapping).length) {
            data = await endpointMapper(
              "inbound",
              JSON.parse(message.value.toString()),
              config.mapping
            ).then((res) => res[0]);
          }

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
        } catch (err) {
          console.log(`Error while doing request: ${err.message}`);
        }
      },
    });
  }
  handleMessages();
}

module.exports = { useKafkaListener };
