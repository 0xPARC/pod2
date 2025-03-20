import { useState } from "react";
import { useNavigate } from "@tanstack/react-router";
import { Button } from "@/components/ui/button";
import { Input } from "@/components/ui/input";
import { Plus } from "lucide-react";
import { api } from "@/lib/api";
import { toast } from "sonner";
import { transformNodeToValue, TreeNode, ValueType } from "@/lib/tree-node";
import { TreeNodeEditor } from "./TreeNodeEditor";

function generateId() {
  return crypto.randomUUID();
}

export function CreateSignedPodEditor() {
  const navigate = useNavigate();
  const [nodes, setNodes] = useState<TreeNode[]>([]);
  const [nickname, setNickname] = useState<string>("");

  async function handleCreatePod() {
    try {
      const key_values = Object.fromEntries(
        nodes.map((node) => [node.key, transformNodeToValue(node)])
      );
      await api.createSignedPod(
        "example-signer",
        key_values,
        nickname || undefined
      );
      toast.success("Signed POD created successfully");
      navigate({ to: "/" });
    } catch (err) {
      console.error("Failed to create Signed POD:", err);
      toast.error("Failed to create Signed POD");
    }
  }

  function addNode() {
    const newNode: TreeNode = {
      id: generateId(),
      key: "",
      type: ValueType.String,
      value: ""
    };
    setNodes([...nodes, newNode]);
  }

  return (
    <div className="container mx-auto py-8">
      <div className="flex justify-between items-center mb-6">
        <h1 className="text-2xl font-bold">Create Signed POD</h1>
        <div className="space-x-2">
          <Button variant="outline" onClick={() => navigate({ to: "/" })}>
            Cancel
          </Button>
          <Button onClick={handleCreatePod}>Create POD</Button>
        </div>
      </div>

      <div className="bg-white rounded-lg shadow p-6">
        <div className="space-y-4">
          <div className="space-y-2">
            <label htmlFor="nickname" className="text-sm font-medium">
              Nickname (optional)
            </label>
            <Input
              id="nickname"
              placeholder="Enter a nickname for this POD"
              value={nickname}
              onChange={(e) => setNickname(e.target.value)}
              className="w-full"
            />
          </div>

          <div className="space-y-2">
            {nodes.length === 0 ? (
              <div className="text-center text-muted-foreground py-8">
                No key-value pairs added yet. Click "Add Key-Value Pair" to
                begin.
              </div>
            ) : (
              nodes.map((node) => (
                <TreeNodeEditor
                  key={node.id}
                  node={node}
                  onUpdate={(updatedNode) => {
                    setNodes(
                      nodes.map((n) => (n.id === node.id ? updatedNode : n))
                    );
                  }}
                  onDelete={() => {
                    setNodes(nodes.filter((n) => n.id !== node.id));
                  }}
                  onAddChild={() => {
                    const newChild: TreeNode = {
                      id: generateId(),
                      key: "",
                      type: ValueType.String,
                      value: ""
                    };
                    setNodes(
                      nodes.map((n) =>
                        n.id === node.id
                          ? {
                              ...n,
                              children: [...(n.children || []), newChild]
                            }
                          : n
                      )
                    );
                  }}
                />
              ))
            )}
            <div className="flex justify-center">
              <Button variant="outline" onClick={addNode}>
                <Plus className="h-4 w-4 mr-2" />
                Add Key-Value Pair
              </Button>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}
