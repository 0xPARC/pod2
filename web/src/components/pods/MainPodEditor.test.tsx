import { render, screen, fireEvent, waitFor } from "@testing-library/react";
import { MainPodEditor } from "./MainPodEditor";
import { api, SignedPod } from "@/lib/api";
import { vi } from "vitest";
import { describe, it, expect, beforeEach } from "vitest";

// Mock the api
vi.mock("@/lib/api", () => ({
  api: {
    listPods: vi.fn(),
    validateStatements: vi.fn(),
    createMainPod: vi.fn()
  }
}));

// Mock the router
vi.mock("@tanstack/react-router", () => ({
  useNavigate: () => vi.fn()
}));

describe("MainPodEditor", () => {
  beforeEach(() => {
    // Reset all mocks before each test
    vi.clearAllMocks();

    // Mock the listPods response
    (api.listPods as unknown as ReturnType<typeof vi.fn>).mockResolvedValue([
      {
        id: "pod1",
        pod_class: "Signed",
        pod_type: "Mock",
        proof: "",
        entries: {
          value1: { Int: 10 },
          value2: { Int: 20 }
        }
      } as SignedPod
    ]);

    // Mock validateStatements to return true
    (
      api.validateStatements as unknown as ReturnType<typeof vi.fn>
    ).mockResolvedValue(true);
  });

  it("renders without crashing", async () => {
    render(<MainPodEditor />);
    expect(await screen.findByText("Create Main POD")).toBeTruthy();
  });

  it("supports adding a MaxOf statement", async () => {
    render(<MainPodEditor />);

    // Click add statement button
    const addButton = await screen.findByText("Add Statement");
    fireEvent.click(addButton);

    // Change statement type to MaxOf
    const typeSelect = await screen.findByText("Equal");
    fireEvent.click(typeSelect);
    const maxOfOption = await screen.findByText("MaxOf");
    fireEvent.click(maxOfOption);

    // Verify that a third argument field appears
    expect(await screen.findByText("Third Argument")).toBeTruthy();
  });

  it("validates three-argument statements correctly", async () => {
    render(<MainPodEditor />);

    // Add a statement
    const addButton = await screen.findByText("Add Statement");
    fireEvent.click(addButton);

    // Change to MaxOf
    const typeSelect = await screen.findByText("Equal");
    fireEvent.click(typeSelect);
    const maxOfOption = await screen.findByText("MaxOf");
    fireEvent.click(maxOfOption);

    // Set first argument
    const firstArgSelect = screen.getAllByText("Select key")[0];
    fireEvent.click(firstArgSelect);
    const firstKeyOption = await screen.findByText("pod1.value1");
    fireEvent.click(firstKeyOption);

    // Set second argument
    const secondArgSelect = screen.getAllByText("Select key")[1];
    fireEvent.click(secondArgSelect);
    const secondKeyOption = await screen.findByText("pod1.value2");
    fireEvent.click(secondKeyOption);

    // Set third argument
    const thirdArgSelect = screen.getAllByText("Select key")[2];
    fireEvent.click(thirdArgSelect);
    const thirdKeyOption = await screen.findByText("pod1.value1");
    fireEvent.click(thirdKeyOption);

    // Verify validation was called with correct arguments
    await waitFor(() => {
      expect(api.validateStatements).toHaveBeenCalledWith(
        expect.arrayContaining([
          expect.objectContaining({
            type: "MaxOf",
            firstArg: expect.any(Object),
            secondArg: expect.any(Object),
            thirdArg: expect.any(Object)
          })
        ])
      );
    });
  });
});
