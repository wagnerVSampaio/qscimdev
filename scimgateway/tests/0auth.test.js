// userRoutes.test.js

const request = require("supertest");
const app = "http://localhost:8880";
const baseURL = `/users`;

describe("Connection", () => {
  const invalidAgent = request.agent(app).auth("invalid", "invalid");

  it("should return status 200", async () => {
    const response = await invalidAgent.get("/ping");

    expect(response.status).toBe(200);
  });

  it("should return an error for unauthorized access", async () => {
    const response = await invalidAgent.get("/Users");

    expect(response.status).toBe(401);
    // expect(response.body).toHaveProperty('schemas');
    // expect(response.body).toHaveProperty('status');
    // expect(response.body).toHaveProperty('detail');
    // expect(response.body.detail).toBe('Unauthorized');
  });
});
