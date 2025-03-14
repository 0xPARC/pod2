import { describe, it, expect, vi } from "vitest";
import { render, screen, fireEvent, waitFor } from "@testing-library/react";
import { CreateSignedPodEditor } from "./CreateSignedPodEditor";
import { api } from "@/lib/api";

// Mock the API
vi.mock("@/lib/api", () => ({
  api: {
    createSignedPod: vi.fn()
  }
}));

// Mock the router
vi.mock("@tanstack/react-router", () => ({
  useNavigate: () => vi.fn()
}));

// Mock sonner
vi.mock("sonner", () => ({
  toast: {
    success: vi.fn(),
    error: vi.fn((message) => {
      const div = document.createElement("div");
      div.textContent = message;
      document.body.appendChild(div);
    })
  }
}));

describe("CreateSignedPodEditor", () => {
  it("should render the editor with initial state", () => {
    render(<CreateSignedPodEditor />);

    expect(screen.getByText("Create Signed POD")).toBeInTheDocument();
    expect(screen.getByText("Add Key-Value Pair")).toBeInTheDocument();
  });

  it("should add a new node when clicking Add Key-Value Pair", () => {
    render(<CreateSignedPodEditor />);

    const addButton = screen.getByText("Add Key-Value Pair");
    fireEvent.click(addButton);

    // Should show a new row with input fields
    expect(screen.getByPlaceholderText("Key")).toBeInTheDocument();
    expect(screen.getByPlaceholderText("Value")).toBeInTheDocument();
  });

  it("should update node type when selecting from dropdown", () => {
    render(<CreateSignedPodEditor />);

    // Add a new node
    fireEvent.click(screen.getByText("Add Key-Value Pair"));

    // Find the type selector and change it to integer
    const typeSelect = screen.getByRole("combobox");
    fireEvent.click(typeSelect);
    fireEvent.click(screen.getByText("Integer"));

    // Verify the value input is still present with the correct placeholder
    expect(screen.getByPlaceholderText("Integer (i64)")).toBeInTheDocument();
  });

  it("should delete a node when clicking delete button", () => {
    render(<CreateSignedPodEditor />);

    // Add a new node
    fireEvent.click(screen.getByText("Add Key-Value Pair"));

    // Delete the node
    const deleteButton = screen.getByRole("button", { name: /delete/i });
    fireEvent.click(deleteButton);

    // Verify the node is removed
    expect(screen.queryByPlaceholderText("Key")).not.toBeInTheDocument();
  });

  it("should create a POD when clicking Create POD", async () => {
    // Mock successful API call
    (api.createSignedPod as any).mockResolvedValueOnce({});

    render(<CreateSignedPodEditor />);

    // Add a test node
    fireEvent.click(screen.getByText("Add Key-Value Pair"));
    fireEvent.change(screen.getByPlaceholderText("Key"), {
      target: { value: "test" }
    });
    fireEvent.change(screen.getByPlaceholderText("Value"), {
      target: { value: "value" }
    });

    // Click create button
    fireEvent.click(screen.getByText("Create POD"));

    // Verify API was called
    await waitFor(() => {
      expect(api.createSignedPod).toHaveBeenCalledWith("example-signer", {
        test: "value"
      });
    });
  });

  it("should show error toast when POD creation fails", async () => {
    // Mock failed API call
    (api.createSignedPod as any).mockRejectedValueOnce(new Error("Failed"));

    render(<CreateSignedPodEditor />);

    // Add a test node
    fireEvent.click(screen.getByText("Add Key-Value Pair"));
    fireEvent.change(screen.getByPlaceholderText("Key"), {
      target: { value: "test" }
    });
    fireEvent.change(screen.getByPlaceholderText("Value"), {
      target: { value: "value" }
    });

    // Click create button
    fireEvent.click(screen.getByText("Create POD"));

    // Verify error toast is shown
    await waitFor(() => {
      expect(
        screen.getByText("Failed to create Signed POD")
      ).toBeInTheDocument();
    });
  });
});
