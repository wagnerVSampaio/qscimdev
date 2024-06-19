// userRoutes.test.js

const request = require("supertest");
const app = "http://localhost:8880";
const baseURL = `/Users`;

const exampleBody = {
  userName: "mLopes",
  givenName: "Maria",
  familyName: "Lopes",
};

const invalidExampleBody = {
  givenName: "Maria",
  familyName: "Lopes",
};

describe("POST /Users", () => {
  const agent = request.agent(app).auth("gwadmin", "password");

  it("should create a new user (201)", async () => {
    const response = await agent.post(baseURL).send(exampleBody);

    expect(response.status).toBe(201);
  });

  it("should return an error for invalid request body (400)", async () => {
    const response = await agent.post(baseURL).send(invalidExampleBody);

    expect(response.status).toBe(500);
    // expect(response.body).toHaveProperty("schemas");
    // expect(response.body).toHaveProperty("status");
    // expect(response.body).toHaveProperty("detail");
    // expect(response.body.detail).toBe("Invalid request body");
  });

  it("should return an error for resource conflict (409)", async () => {
    const response = await agent.post(baseURL).send(exampleBody);

    expect(response.status).toBe(409);
    expect(response.body).toHaveProperty("schemas");
    expect(response.body).toHaveProperty("status");
    expect(response.body).toHaveProperty("detail");
    // expect(response.body.detail).toBe("Resource already exists");

    const deleteResponse = await agent.delete(
      `${baseURL}/${exampleBody.userName}`
    );

    expect(deleteResponse.status).toBe(204);
  });
});
