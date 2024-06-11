let form = document.getElementById("form");
  const submitBtn = document.getElementById("submit_btn");
  
  form.addEventListener("submit", async (e) => {
    e.preventDefault();
    const selectedConnectors = [];
  
    await formHandler(e, form, submitBtn, selectedConnectors);
  });
  