// userRoutes.test.js

const request = require("supertest");
const app = "http://localhost:8880"; 
const baseURL = `/Users`;

describe("GET /Users", () => {
  const agent = request.agent(app).auth("gwadmin", "password");
  const invalidAgent = request.agent(app).auth("invalid", "invalid");

  it("should return a list of users", async () => {
    const response = await agent.get(baseURL);

    expect(response.status).toBe(200);
    expect(response.body).toHaveProperty("schemas");
    expect(response.body).toHaveProperty("totalResults");
    expect(response.body).toHaveProperty("startIndex");
    expect(response.body).toHaveProperty("itemsPerPage");
    expect(response.body).toHaveProperty("Resources");
  });

  it("should return an error for unauthorized access", async () => {
    const response = await invalidAgent.get(baseURL);

    expect(response.status).toBe(401);
    // expect(response.body).toHaveProperty('schemas');
    // expect(response.body).toHaveProperty('status');
    // expect(response.body).toHaveProperty('detail');
    // expect(response.body.detail).toBe('Unauthorized');
  });
});
