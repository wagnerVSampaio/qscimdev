// userRoutes.test.js

const request = require("supertest");
const app = "http://localhost:8880";
const baseURL = `/Groups`;

const exampleBody = {
  displayName: "newGroup",
};

const invalidExampleBody = {};

describe("POST /Groups", () => {
  const agent = request.agent(app).auth("gwadmin", "password");

  // it("should create a new group (201)", async () => {
  //   const response = await agent.post(baseURL).send(exampleBody);

  //   expect(response.status).toBe(201);
  //   expect(response.body).toHaveProperty("id");
  //   // expect(response.body).toHaveProperty("displayName");
  //   // expect(response.body).toHaveProperty("schemas");
  // });


  // it("should return an error for conflict (409)", async () => {
  //   const response = await agent.post(baseURL).send(exampleBody);

  //   expect(response.status).toBe(409);
  //   // You can add specific error message expectations based on your implementation
  // });
});
