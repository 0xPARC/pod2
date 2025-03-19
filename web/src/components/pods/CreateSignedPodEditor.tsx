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
import { TreeNode, ValueType } from "@/lib/types";

function generateId() {
  return crypto.randomUUID();
}

export function TreeNodeEditor({
  node,
  onUpdate,
  onDelete,
  onAddChild,
  level = 0,
  parentType,
  hideKey = false,
  hideDelete = false
}: {
  node: TreeNode;
  onUpdate: (node: TreeNode) => void;
  onDelete: () => void;
  onAddChild: () => void;
  level?: number;
  parentType?: ValueType;
  hideKey?: boolean;
  hideDelete?: boolean;
}) {
  const [isExpanded, setIsExpanded] = useState(true);
  const hasChildren =
    node.type === ValueType.Array ||
    node.type === ValueType.Set ||
    node.type === ValueType.Dictionary;

  // Show key input if:
  // 1. This is a dictionary child (parent is dictionary)
  // 2. This is a top-level item (no parent)
  // 3. Keys are not hidden
  const shouldShowKey =
    (parentType === ValueType.Dictionary || !parentType) && !hideKey;

  function handleTypeChange(type: ValueType) {
    onUpdate({
      ...node,
      type,
      value:
        type === ValueType.Array
          ? []
          : type === ValueType.Set
            ? new Set()
            : type === ValueType.Dictionary
              ? {}
              : "",
      children:
        type === ValueType.Array ||
        type === ValueType.Set ||
        type === ValueType.Dictionary
          ? []
          : undefined
    });
  }

  const handleValueChange = (value: string) => {
    if (node.type === ValueType.Int) {
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
            <SelectItem value={ValueType.String}>String</SelectItem>
            <SelectItem value={ValueType.Int}>Integer</SelectItem>
            <SelectItem value={ValueType.Bool}>Boolean</SelectItem>
            <SelectItem value={ValueType.Array}>Array</SelectItem>
            <SelectItem value={ValueType.Set}>Set</SelectItem>
            <SelectItem value={ValueType.Dictionary}>Dictionary</SelectItem>
          </SelectContent>
        </Select>
        {!hasChildren &&
          (node.type === ValueType.Bool ? (
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
              placeholder={
                node.type === ValueType.Int ? "Integer (i64)" : "Value"
              }
              value={String(node.value)}
              onChange={(e) => handleValueChange(e.target.value)}
              className="w-48"
              type={node.type === ValueType.Int ? "text" : "text"}
            />
          ))}
        {!hideDelete && (
          <Button
            variant="ghost"
            size="icon"
            onClick={onDelete}
            aria-label="Delete"
          >
            <Trash2 className="h-4 w-4" />
          </Button>
        )}
        {hasChildren && (
          <Button variant="ghost" size="icon" onClick={onAddChild}>
            <Plus className="h-4 w-4" />
          </Button>
        )}
      </div>
      {hasChildren && isExpanded && node.children && (
        <div className="space-y-2 pl-4">
          {node.type === ValueType.Array && node.children ? (
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
                                  type: ValueType.String,
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
                    type: ValueType.String,
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
