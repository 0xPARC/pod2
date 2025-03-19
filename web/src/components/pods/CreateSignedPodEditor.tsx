import { useState } from "react";
import { useNavigate } from "@tanstack/react-router";
import { Button } from "@/components/ui/button";
import { Input } from "@/components/ui/input";
import {
  Select,
  SelectContent,
  SelectItem,
  SelectTrigger,
  SelectValue
} from "@/components/ui/select";
import {
  ChevronDown,
  ChevronRight,
  Plus,
  Trash2,
  GripVertical
} from "lucide-react";
import { api } from "@/lib/api";
import { toast } from "sonner";
import {
  DragDropContext,
  Droppable,
  Draggable,
  DropResult
} from "@hello-pangea/dnd";
import { serializePodTree, numberToString } from "@/lib/pod-serialization";

export type ValueType =
  | "string"
  | "integer"
  | "boolean"
  | "array"
  | "set"
  | "dictionary";

type PrimitiveValue = string | number | boolean;
type ArrayValue = PrimitiveValue[];
type SetValue = Set<PrimitiveValue>;
type DictionaryValue = Record<string, PrimitiveValue | ArrayValue | SetValue>;
type PodValue = PrimitiveValue | ArrayValue | SetValue | DictionaryValue;

export interface TreeNode {
  id: string;
  key: string;
  type: ValueType;
  value: PodValue;
  children?: TreeNode[];
}

function generateId() {
  return Math.random().toString(36).substring(2, 9);
}

export function TreeNodeEditor({
  node,
  onUpdate,
  onDelete,
  onAddChild,
  level = 0,
  parentType
}: {
  node: TreeNode;
  onUpdate: (node: TreeNode) => void;
  onDelete: () => void;
  onAddChild: () => void;
  level?: number;
  parentType?: ValueType;
}) {
  const [isExpanded, setIsExpanded] = useState(true);
  const hasChildren =
    node.type === "array" || node.type === "set" || node.type === "dictionary";

  // Show key input if:
  // 1. This is a dictionary child (parent is dictionary)
  // 2. This is a top-level item (no parent)
  const shouldShowKey = parentType === "dictionary" || !parentType;

  function handleTypeChange(type: ValueType) {
    onUpdate({
      ...node,
      type,
      value:
        type === "array"
          ? []
          : type === "set"
          ? new Set()
          : type === "dictionary"
          ? {}
          : "",
      children:
        type === "array" || type === "set" || type === "dictionary"
          ? []
          : undefined
    });
  }

  const handleValueChange = (value: string) => {
    if (node.type === "integer") {
      try {
        // This will validate the number is within i64 bounds
        numberToString(value);
        onUpdate({ ...node, value: value });
      } catch (err) {
        if (err instanceof Error) {
          toast.error(err.message);
        }
        // Keep the old value
        return;
      }
    } else {
      onUpdate({ ...node, value });
    }
  };

  function handleDragEnd(result: DropResult) {
    if (!result.destination || !node.children) return;

    const items = Array.from(node.children);
    const [reorderedItem] = items.splice(result.source.index, 1);
    items.splice(result.destination.index, 0, reorderedItem);

    onUpdate({ ...node, children: items });
  }

  return (
    <div style={{ marginLeft: `${level * 12}px` }}>
      <div className="flex items-center gap-2 py-2">
        {hasChildren ? (
          <div className="flex items-center gap-2">
            <Button
              variant="ghost"
              size="icon"
              onClick={() => setIsExpanded(!isExpanded)}
            >
              {isExpanded ? (
                <ChevronDown className="h-4 w-4" />
              ) : (
                <ChevronRight className="h-4 w-4" />
              )}
            </Button>
          </div>
        ) : (
          <div className="w-9" />
        )}
        {shouldShowKey && (
          <Input
            placeholder="Key"
            value={node.key}
            onChange={(e) => onUpdate({ ...node, key: e.target.value })}
            className="w-48"
          />
        )}
        <Select value={node.type} onValueChange={handleTypeChange}>
          <SelectTrigger className="w-32">
            <SelectValue />
          </SelectTrigger>
          <SelectContent>
            <SelectItem value="string">String</SelectItem>
            <SelectItem value="integer">Integer</SelectItem>
            <SelectItem value="boolean">Boolean</SelectItem>
            <SelectItem value="array">Array</SelectItem>
            <SelectItem value="set">Set</SelectItem>
            <SelectItem value="dictionary">Dictionary</SelectItem>
          </SelectContent>
        </Select>
        {!hasChildren &&
          (node.type === "boolean" ? (
            <Select
              value={String(node.value)}
              onValueChange={(value) => handleValueChange(value)}
            >
              <SelectTrigger className="w-32">
                <SelectValue />
              </SelectTrigger>
              <SelectContent>
                <SelectItem value="true">True</SelectItem>
                <SelectItem value="false">False</SelectItem>
              </SelectContent>
            </Select>
          ) : (
            <Input
              placeholder={node.type === "integer" ? "Integer (i64)" : "Value"}
              value={String(node.value)}
              onChange={(e) => handleValueChange(e.target.value)}
              className="w-48"
              type={node.type === "integer" ? "text" : "text"}
            />
          ))}
        <Button
          variant="ghost"
          size="icon"
          onClick={onDelete}
          aria-label="Delete"
        >
          <Trash2 className="h-4 w-4" />
        </Button>
        {hasChildren && (
          <Button variant="ghost" size="icon" onClick={onAddChild}>
            <Plus className="h-4 w-4" />
          </Button>
        )}
      </div>
      {hasChildren && isExpanded && node.children && (
        <div className="space-y-2 pl-4">
          {node.type === "array" && node.children ? (
            <DragDropContext onDragEnd={handleDragEnd}>
              <Droppable droppableId={node.id}>
                {(provided) => (
                  <div
                    {...provided.droppableProps}
                    ref={provided.innerRef}
                    className="space-y-2"
                  >
                    {(node.children || []).map((child, index) => (
                      <Draggable
                        key={child.id}
                        draggableId={child.id}
                        index={index}
                      >
                        {(provided) => (
                          <div
                            ref={provided.innerRef}
                            {...provided.draggableProps}
                            className="flex items-center gap-2"
                          >
                            <div
                              {...provided.dragHandleProps}
                              className="cursor-grab"
                            >
                              <GripVertical className="h-4 w-4" />
                            </div>
                            <TreeNodeEditor
                              node={child}
                              onUpdate={(updatedChild) => {
                                const newChildren = node.children?.map((c) =>
                                  c.id === child.id ? updatedChild : c
                                );
                                onUpdate({ ...node, children: newChildren });
                              }}
                              onDelete={() => {
                                const newChildren = node.children?.filter(
                                  (c) => c.id !== child.id
                                );
                                onUpdate({ ...node, children: newChildren });
                              }}
                              onAddChild={() => {
                                const newChild: TreeNode = {
                                  id: generateId(),
                                  key: "",
                                  type: "string",
                                  value: ""
                                };
                                onUpdate({
                                  ...node,
                                  children: [...(node.children || []), newChild]
                                });
                              }}
                              level={0}
                              parentType={node.type}
                            />
                          </div>
                        )}
                      </Draggable>
                    ))}
                    {provided.placeholder}
                  </div>
                )}
              </Droppable>
            </DragDropContext>
          ) : (
            node.children?.map((child) => (
              <TreeNodeEditor
                key={child.id}
                node={child}
                onUpdate={(updatedChild) => {
                  const newChildren = node.children?.map((c) =>
                    c.id === child.id ? updatedChild : c
                  );
                  onUpdate({ ...node, children: newChildren });
                }}
                onDelete={() => {
                  const newChildren = node.children?.filter(
                    (c) => c.id !== child.id
                  );
                  onUpdate({ ...node, children: newChildren });
                }}
                onAddChild={() => {
                  const newChild: TreeNode = {
                    id: generateId(),
                    key: "",
                    type: "string",
                    value: ""
                  };
                  onUpdate({
                    ...node,
                    children: [...(node.children || []), newChild]
                  });
                }}
                level={0}
                parentType={node.type}
              />
            ))
          )}
        </div>
      )}
    </div>
  );
}

export function CreateSignedPodEditor() {
  const navigate = useNavigate();
  const [nodes, setNodes] = useState<TreeNode[]>([]);
  const [nickname, setNickname] = useState<string>("");

  async function handleCreatePod() {
    try {
      const { key_values } = serializePodTree(nodes);
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
      type: "string",
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
                      type: "string",
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
