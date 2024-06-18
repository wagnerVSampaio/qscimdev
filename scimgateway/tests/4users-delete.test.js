// userRoutes.test.js

const request = require("supertest");
const app = "http://localhost:8880";
const baseURL = `/Users`;

describe("DELETE /Users${id}", () => {
  const agent = request.agent(app).auth("gwadmin", "password");

  it("should delete an existing user (204)", async () => {
    let createdUser = await agent.post(baseURL).send({
      userName: "toDelete",
    });
    let userId = createdUser.body.userName;

    const response = await agent.delete(`${baseURL}/${userId}`);

    expect(response.status).toBe(204);
  });

  // it("should return an error for invalid request (400)", async () => {
  //   const response = await agent.delete("/Users/abc123"); // ID inválido

  //   expect(response.status).toBe(400);
  //   expect(response.body).toHaveProperty("schemas");
  //   expect(response.body).toHaveProperty("status");
  //   expect(response.body).toHaveProperty("detail");
  //   expect(response.body.detail).toBe("Invalid request");
  // });

  // it("should return an error for not found (404)", async () => {
  //   const response = await agent.delete("/Users/9876543210"); // Usuário inexistente

  //   expect(response.status).toBe(404);
  //   // expect(response.body).toHaveProperty("schemas");
  //   // expect(response.body).toHaveProperty("status");
  //   // expect(response.body).toHaveProperty("detail");
  //   // expect(response.body.detail).toBe("Resource not found");
  // });
});
