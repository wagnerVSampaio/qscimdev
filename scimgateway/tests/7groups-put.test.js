const request = require("supertest");
const app = "http://localhost:8880"; // Assuming your groups API is at the same port
const baseURL = "/Groups";

const exampleBody = {
  displayName: "Updated Group Name",
};

describe("PUT /Groups/{id}", () => {
  const agent = request.agent(app).auth("gwadmin", "password");

  // it("should update an existing group (200)", async () => {
  //   const createdGroup = await agent.post(baseURL).send(exampleBody);
  //   let groupId = createdGroup.body.id;

  //   const response = await agent.put(`${baseURL}/${groupId}`).send(exampleBody);

  //   expect(response.status).toBe(200);
  //   expect(response.body).toHaveProperty("schemas");
  //   expect(response.body).toHaveProperty("id", groupId); // Updated ID should match
  //   expect(response.body).toHaveProperty("displayName", "Updated Group Name");
  // });

  // it("should return an error for not found (404)", async () => {
  //   const response = await agent.put(`${baseURL}/not_found`).send(exampleBody);

  //   expect(response.status).toBe(404);
  //   // You can add specific error message expectations based on your implementation
  // });

  // it("should return an error for invalid request body (400)", async () => {
  //   const invalidData = {}; // Missing required fields
  //   const response = await agent.put(`${baseURL}/${groupId}`).send(invalidData);

  //   expect(response.status).toBe(400);
  //   // You can add specific error message expectations based on your implementation
  // });
});
