const request = require("supertest");
const app = "http://localhost:8880"; // Assuming your groups API is at the same port
const baseURL = "/Groups";

describe("DELETE /Groups/{id}", () => {
  const agent = request.agent(app).auth("gwadmin", "password");

  // it("should delete an existing group (204)", async () => {
  //   let createdGroup = await agent.post(baseURL).send({
  //     displayName: "deleteGroup",
  //   });
  //   let groupId = createdGroup.body.id;

  //   const response = await agent.delete(`${baseURL}/${groupId}`);

  //   expect(response.status).toBe(204);
  // });

  // it("should return an error for not found (404)", async () => {
  //   const response = await agent.delete(`${baseURL}/not_found`); // Non-existent group

  //   expect(response.status).toBe(404);
  //   // You can add specific error message expectations based on your implementation
  // });
});
