const baseUrl = "http://host.docker.internal";
  function showMessage(type, description) {
    var messageContainer = document.getElementById('messageContainer');
    var messageDiv = document.createElement('div');
    messageDiv.className = 'message ' + type;
    switch (type) {
      case 'success':
        messageDiv.textContent = 'Form submitted successfully';
        break;
      case 'error':
        messageDiv.textContent = 'Form submitted error: ' + description;
        break;
      case 'warning':
        messageDiv.textContent = 'This is a warning message';
        break;
      default:
        break;
    }
    messageContainer.appendChild(messageDiv);
    setTimeout(function () {
      messageDiv.remove();
    }, 3000); 
  }

  async function formHandler(e, form, submitBtn, selectedConnectors) {
    submitBtn.innerHTML = "...";
    submitBtn.disabled = true;
    let body = {};
    try {
      Array.from(form.elements).forEach((el) => {
        let name = el.id.split("_").slice(1).join("_");
        let value;
        switch (el.tagName.toLowerCase()) {
          case "button":
            return;
          case "input":
            value = el.type === "checkbox" ? el.checked : el.value;
            body[name] = value;
            return;
          case "select":
            body[name] = el.value;
            return;
          default:
            body[name] = el.value;
            return;
        }
      });
  
      const promises = selectedConnectors.map(async (item) => {
        return fetch(`${baseUrl}${item.url}`, {
          method: item.method,
          headers: item.headers,
          body: JSON.stringify(body),
        }).then(async (response) => {
          if (response.ok) {
            return response.json();
          } else {
            console.error(await response.json());
            throw new Error("Failed to fetch");
          }
        });
      });
  
      await Promise.all(promises).catch((error) => {
        throw new Error(error);
      });
      showMessage("sucess")
      window.location.href = "card.html";
    } catch (error) {
      showMessage("error", error.message)
      console.error(error);
    } finally {
      submitBtn.innerHTML = "Submit";
      submitBtn.disabled = false;
    }
  }
  
  module.exports = { baseUrl, formHandler };
  