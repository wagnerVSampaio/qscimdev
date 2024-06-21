const axios = require("axios");

const getToken = async (auth, url) => {
  try {
    console.log(auth)
    const response = await axios.post(
      url ? `${url}/oauth/token` : "/oatuh/token",
      {
        grant_type: "client_credentials",
        scope:
          "channels:read users:read users.profile:read dnd:read bookmarks:read reactions:read team:read emoji:read calls:read im:read groups:read chat:write",
      },
      {
        auth: {
          username: auth?.client_id,
          password: auth?.client_secret,
        },
      }
    );

    const { access_token, expires_in } = response.data;
    const expirationTime = new Date().getTime() + expires_in * 1000;

    return { access_token, expirationTime };
  } catch (error) {
    console.error("Error fetching OAuth2 token:", error);
    throw error;
  }
};

async function formatAuth(auth, url) {
  if (!auth) return { token: undefined };

  switch (auth.type) {
    case "bearer":
      return { token: "Bearer " + auth.token };
    case "basic":
      return {
        token: "Basic " + btoa(`${auth.username}:${auth.password}`),
      };
    case "oauth2":
      const { access_token, expirationTime } = await getToken(auth, url);
      return { token: "Bearer " + access_token, expirationTime };
    default:
      return { token: undefined };
  }
}

module.exports = { formatAuth };
