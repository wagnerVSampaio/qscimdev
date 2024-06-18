const rules = [{
  "port": "8881",
  "type": "all",
  "block_on_error": true,
  "conditions": [
    {
      "fact": "",
      "operator": "equal",
      "value": ""
    }
  ],
  "allowed_requests": [
    {
      "path": "users",
      "method": "POST"
    }
  ],
  "position": 0
}];
            
module.exports = { rules };