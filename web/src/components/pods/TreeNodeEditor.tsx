import { useState } from "react";
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
import { toast } from "sonner";
import {
  DragDropContext,
  Droppable,
  Draggable,
  DropResult
} from "@hello-pangea/dnd";
import { TreeNode, ValueType } from "@/lib/tree-node";
import { PODValue } from "@/lib/core-types";
import { numberToString } from "@/lib/pod-serialization";

function generateId() {
  return crypto.randomUUID();
}

function displayValue(value: PODValue): string {
  if (typeof value === "string") return value;
  if (typeof value === "boolean") return String(value);
  if ("Int" in value) return value.Int;
  if ("Raw" in value) return value.Raw;
  if ("Set" in value) return `Set(${value.Set.length} items)`;
  if ("Dictionary" in value)
    return `Dict(${Object.keys(value.Dictionary).length} items)`;
  if (Array.isArray(value)) return `Array(${value.length} items)`;
  return "";
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
            ? { Set: [] }
            : type === ValueType.Dictionary
              ? { Dictionary: {} }
              : type === ValueType.Int
                ? { Int: "0" }
                : type === ValueType.Raw
                  ? { Raw: "" }
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
        onUpdate({ ...node, value: { Int: value } });
      } catch (err) {
        if (err instanceof Error) {
          toast.error(err.message);
        }
        // Keep the old value
        return;
      }
    } else if (node.type === ValueType.Raw) {
      onUpdate({ ...node, value: { Raw: value } });
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
            <SelectItem value={ValueType.Raw}>Raw</SelectItem>
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
              value={displayValue(node.value)}
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
