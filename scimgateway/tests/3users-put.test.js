// userRoutes.test.js

const request = require("supertest");
const app = "http://localhost:8880";
const baseURL = `/Users`;

const createBody = {
  userName: "updateUser",
  givenName: "Maria",
  familyName: "Lopes",
};

const updateBody = {
  givenName: "Maria",
  familyName: "Lopes",
};

describe("PUT /Users/${id}", () => {
  const agent = request.agent(app).auth("gwadmin", "password");

  it("should update an existing user (200)", async () => {
    const createdUser = await agent.post(baseURL).send(createBody);

    const response = await agent
      .put(`${baseURL}/${createdUser.body.userName}`)
      .send(updateBody);

    expect(response.status).toBe(200);

    const deleteResponse = await agent.delete(
      `${baseURL}/${createdUser.body.userName}`
    );

    expect(deleteResponse.status).toBe(204);
  });

  // it("should return an error for invalid request body (400)", async () => {
  //   const response = await agent.put("/Users/1234567890").send(exampleBody);

  //   expect(response.status).toBe(400);
  //   expect(response.body).toHaveProperty("schemas");
  //   expect(response.body).toHaveProperty("status");
  //   expect(response.body).toHaveProperty("detail");
  //   expect(response.body.detail).toBe("Invalid request body");
  // });

  // it("should return an error for not found (404)", async () => {
  //   const response = await agent.put("/Users/not_found").send(exampleBody);

  //   expect(response.status).toBe(404);
  //   // expect(response.body).toHaveProperty("schemas");
  //   // expect(response.body).toHaveProperty("status");
  //   // expect(response.body).toHaveProperty("detail");
  //   // expect(response.body.detail).toBe("Resource not found");
  // });
});
