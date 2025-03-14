import { vi } from "vitest";

export const toast = {
  success: vi.fn(),
  error: vi.fn((message) => {
    // Create a div with the error message for testing
    const div = document.createElement("div");
    div.textContent = message;
    document.body.appendChild(div);
  })
};
