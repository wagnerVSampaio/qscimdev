// userRoutes.test.js

const request = require("supertest");
const app = "http://localhost:8880";
const baseURL = `/Groups`;

describe("GET /Groups", () => {
  const agent = request.agent(app).auth("gwadmin", "password");
  const invalidAgent = request.agent(app).auth("invalid", "invalid");

  it("should return a list of groups", async () => {
    const response = await agent.get(baseURL);

    expect(response.status).toBe(200);
    expect(response.body).toHaveProperty("schemas");
    expect(response.body).toHaveProperty("totalResults");
    expect(response.body).toHaveProperty("Resources"); // Groups instead of Users
  });
});
