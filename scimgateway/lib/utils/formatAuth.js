function formatAuth(auth) {
  switch (auth.type) {
    case "bearer":
      return "Bearer " + auth.token;
    case "basic":
      return "Basic " + btoa(`${auth.username}:${auth.password}`);
    default:
      return "";
  }
}

module.exports = { formatAuth };
