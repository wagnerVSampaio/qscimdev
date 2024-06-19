let form = document.getElementById("form");
  const submitBtn = document.getElementById("submit_btn");
  
  form.addEventListener("submit", async (e) => {
    e.preventDefault();
    const selectedConnectors = [{
        url: ":8889/users",
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          Authorization: "Basic " + btoa("wagner:1236"),
        },
      }];
  
    await formHandler(e, form, submitBtn, selectedConnectors);
  });
  