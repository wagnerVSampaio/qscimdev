
    const tracingConfig = {
  "name": "QSCIM Tracing",
  "url": "http://localhost:9411/api/v2/spans",
  "enabled": false,
  "paths": [
    "users",
    "groups"
  ],
  "methods": [
    "GET",
    "POST",
    "PUT",
    "PATCH",
    "DELETE"
  ]
}
    
    module.exports = { tracingConfig }