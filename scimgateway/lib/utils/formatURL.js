// replacing {{text}} variables in string to body values
function formatURL(body, url) {
  const replaceKey = (match, key) => {
    // Verify if key exists in body
    if (body[key]) {
      return body[key];
    }

    // throw an error if key does not exist
    throw new Error(`Missing required field ${key} in body`);
  };

  return url.replace(/{{(.*?)}}/g, replaceKey);
}

module.exports = { formatURL };
