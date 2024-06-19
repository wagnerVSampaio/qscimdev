const requests = [{
  "port": "8889",
  "method": "GET",
  "allowed_requests": [
    {
      "path": "users",
      "method": "POST"
    }
  ],
  "mapping": [],
  "auth": {
    "type": "none"
  },
  "position": 0
}];
            
module.exports = { requests };