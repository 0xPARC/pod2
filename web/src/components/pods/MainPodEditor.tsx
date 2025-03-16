import { useState, useEffect } from "react";
import { Button } from "@/components/ui/button";
import {
  Select,
  SelectContent,
  SelectItem,
  SelectTrigger,
  SelectValue
} from "@/components/ui/select";
import { Plus, Trash2, CheckCircle2, XCircle, Loader2 } from "lucide-react";
import { Card, CardContent } from "@/components/ui/card";
import {
  api,
  Pod,
  EditorStatement,
  StatementType,
  isSignedPod,
  TreeNode,
  KeyValue,
  isKeyValue
} from "@/lib/api";
import { useDebounce } from "@/lib/hooks/useDebounce";
import { useNavigate } from "@tanstack/react-router";
import { toast } from "sonner";

// Simple TreeNodeEditor component
function TreeNodeEditor({
  node,
  onUpdate
}: {
  node: TreeNode;
  onUpdate: (node: TreeNode) => void;
}) {
  return (
    <div>
      <input
        type="text"
        value={String(node.value)}
        onChange={(e) => onUpdate({ ...node, value: e.target.value })}
      />
    </div>
  );
}

export function MainPodEditor() {
  const [statements, setStatements] = useState<EditorStatement[]>([]);
  const [validationState, setValidationState] = useState<{
    isPending: boolean;
    isValid?: boolean;
  }>({ isPending: false });
  const [pods, setPods] = useState<Pod[]>([]);
  const debouncedStatements = useDebounce(statements, 500);
  const navigate = useNavigate();

  // Load available PODs
  useEffect(() => {
    api.listPods().then(setPods);
  }, []);

  function isStatementComplete(statement: EditorStatement): boolean {
    // Check first argument
    if (!statement.firstArg.wildcardId.value || !statement.firstArg.key) {
      return false;
    }

    // Check second argument
    if (statement.secondArg.type === "key") {
      return !!(
        statement.secondArg.value.podId && statement.secondArg.value.key
      );
    } else {
      return statement.secondArg.value.value !== "";
    }
  }

  // Validate statements when they change
  useEffect(() => {
    const validateStatements = async () => {
      if (debouncedStatements.length === 0) return;

      // Only validate if all statements are complete
      if (!debouncedStatements.every(isStatementComplete)) return;

      // Set validation state to pending
      setValidationState({ isPending: true });

      try {
        const isValid = await api.validateStatements(debouncedStatements);
        setValidationState({ isPending: false, isValid });
      } catch (error) {
        console.error("Validation error:", error);
        setValidationState({ isPending: false, isValid: false });
      }
    };

    validateStatements();
  }, [debouncedStatements]);

  function handleAddStatement() {
    const newStatement: EditorStatement = {
      id: crypto.randomUUID(),
      type: "Equal",
      firstArg: {
        wildcardId: { type: "concrete", value: "" },
        key: ""
      },
      secondArg: {
        type: "key",
        value: { podId: "", podClass: "Signed", key: "" }
      }
    };
    setStatements([...statements, newStatement]);
  }

  function handleDeleteStatement(id: string) {
    setStatements(statements.filter((s) => s.id !== id));
  }

  function handleStatementTypeChange(id: string, type: StatementType) {
    setStatements(statements.map((s) => (s.id === id ? { ...s, type } : s)));
  }

  function handleFirstArgChange(
    id: string,
    arg: { podId: string; podClass: string; key: string }
  ) {
    setStatements(
      statements.map((s) =>
        s.id === id
          ? {
              ...s,
              firstArg: {
                wildcardId: { type: "concrete", value: arg.podId },
                key: arg.key
              }
            }
          : s
      )
    );
  }

  function handleSecondArgTypeChange(id: string, type: "key" | "literal") {
    setStatements(
      statements.map((s) =>
        s.id === id
          ? {
              ...s,
              secondArg:
                type === "key"
                  ? {
                      type: "key",
                      value: { podId: "", podClass: "Signed", key: "" }
                    }
                  : {
                      type: "literal",
                      value: {
                        id: crypto.randomUUID(),
                        key: "",
                        type: "string",
                        value: ""
                      }
                    }
            }
          : s
      )
    );
  }

  function handleSecondArgAnchoredKeyChange(id: string, arg: KeyValue) {
    setStatements(
      statements.map((s) =>
        s.id === id &&
        s.secondArg.type === "key" &&
        isKeyValue(s.secondArg.value)
          ? {
              ...s,
              secondArg: {
                type: "key",
                value: arg
              }
            }
          : s
      )
    );
  }

  function handleSecondArgLiteralChange(id: string, node: TreeNode) {
    setStatements(
      statements.map((s) =>
        s.id === id
          ? {
              ...s,
              secondArg: {
                type: "literal",
                value: node
              }
            }
          : s
      )
    );
  }

  async function handleCreateMainPod() {
    try {
      await api.createMainPod(statements);
      toast.success("Main POD created successfully");
      // Navigate back to the pods list on success
      navigate({ to: "/" });
    } catch (error) {
      console.error("Failed to create Main POD:", error);
      toast.error("Failed to create Main POD");
    }
  }

  return (
    <div className="container mx-auto py-8">
      <div className="flex items-center justify-between mb-6">
        <h1 className="text-2xl font-bold">Create Main POD</h1>
        <div className="flex gap-4">
          <Button onClick={handleAddStatement}>
            <Plus className="w-4 h-4 mr-2" />
            Add Statement
          </Button>
          <Button
            onClick={handleCreateMainPod}
            disabled={!validationState.isValid || validationState.isPending}
            variant="default"
          >
            Create Main POD
          </Button>
        </div>
      </div>

      <div className="bg-white rounded-lg shadow p-6">
        <div className="space-y-4">
          {statements.map((statement) => (
            <Card key={statement.id}>
              <CardContent className="pt-6">
                <div className="space-y-4">
                  <div className="flex items-center justify-between">
                    <div className="flex items-center gap-4">
                      <div className="flex items-center gap-2">
                        <span className="text-sm font-medium">
                          Statement Type
                        </span>
                      </div>
                      <Select
                        value={statement.type}
                        onValueChange={(value) =>
                          handleStatementTypeChange(
                            statement.id,
                            value as StatementType
                          )
                        }
                      >
                        <SelectTrigger className="w-[180px]">
                          <SelectValue placeholder="Select type" />
                        </SelectTrigger>
                        <SelectContent>
                          <SelectItem value="Equal">Equal</SelectItem>
                          <SelectItem value="NotEqual">NotEqual</SelectItem>
                          <SelectItem value="Gt">Gt</SelectItem>
                          <SelectItem value="Lt">Lt</SelectItem>
                          <SelectItem value="Contains">Contains</SelectItem>
                          <SelectItem value="NotContains">
                            NotContains
                          </SelectItem>
                        </SelectContent>
                      </Select>
                    </div>
                    <div className="flex items-center gap-2">
                      {validationState.isPending ? (
                        <Loader2 className="w-4 h-4 animate-spin text-muted-foreground" />
                      ) : validationState.isValid ? (
                        <CheckCircle2 className="w-4 h-4 text-green-500" />
                      ) : validationState.isValid === false ? (
                        <XCircle className="w-4 h-4 text-red-500" />
                      ) : null}
                      <Button
                        variant="ghost"
                        size="icon"
                        onClick={() => handleDeleteStatement(statement.id)}
                      >
                        <Trash2 className="w-4 h-4" />
                      </Button>
                    </div>
                  </div>

                  <div className="flex items-center gap-4">
                    <div className="flex items-center gap-2">
                      <span className="text-sm font-medium">
                        First Argument
                      </span>
                    </div>
                    <Select
                      value={`${statement.firstArg.wildcardId.value}:${statement.firstArg.key}`}
                      onValueChange={(value) => {
                        const [wildcardId, key] = value.split(":");
                        const pod = pods.find((p) => p.id === wildcardId);
                        if (pod) {
                          handleFirstArgChange(statement.id, {
                            podId: wildcardId,
                            podClass: pod.pod_class,
                            key
                          });
                        }
                      }}
                    >
                      <SelectTrigger className="w-[180px]">
                        <SelectValue placeholder="Select key" />
                      </SelectTrigger>
                      <SelectContent>
                        {pods.map(
                          (pod) =>
                            isSignedPod(pod) &&
                            Object.entries(pod.entries).map(([key]) => (
                              <SelectItem
                                key={`${pod.id}:${key}`}
                                value={`${pod.id}:${key}`}
                              >
                                {pod.id}.{key}
                              </SelectItem>
                            ))
                        )}
                      </SelectContent>
                    </Select>
                    {statement.firstArg.wildcardId.value &&
                      statement.firstArg.key && (
                        <span className="text-sm text-muted-foreground">
                          {(() => {
                            const pod = pods.find(
                              (p) =>
                                p.id === statement.firstArg.wildcardId.value
                            );
                            if (isSignedPod(pod)) {
                              return (
                                pod.entries[
                                  statement.firstArg.key
                                ]?.toString() || "N/A"
                              );
                            }
                            return "N/A";
                          })()}
                        </span>
                      )}
                  </div>

                  <div className="flex items-center gap-4">
                    <div className="flex items-center gap-2">
                      <span className="text-sm font-medium">
                        Second Argument
                      </span>
                    </div>
                    <Select
                      value={statement.secondArg.type}
                      onValueChange={(value) =>
                        handleSecondArgTypeChange(
                          statement.id,
                          value as "key" | "literal"
                        )
                      }
                    >
                      <SelectTrigger className="w-[180px]">
                        <SelectValue placeholder="Select type" />
                      </SelectTrigger>
                      <SelectContent>
                        <SelectItem value="key">Anchored Key</SelectItem>
                        <SelectItem value="literal">Literal Value</SelectItem>
                      </SelectContent>
                    </Select>

                    {statement.secondArg.type === "key" && (
                      <>
                        <Select
                          value={
                            isKeyValue(statement.secondArg.value)
                              ? `${statement.secondArg.value.podId}:${statement.secondArg.value.key}`
                              : ""
                          }
                          onValueChange={(value) => {
                            const [podId, key] = value.split(":");
                            const pod = pods.find((p) => p.id === podId);
                            if (pod) {
                              handleSecondArgAnchoredKeyChange(statement.id, {
                                podId,
                                podClass: pod.pod_class,
                                key
                              });
                            }
                          }}
                        >
                          <SelectTrigger className="w-[180px]">
                            <SelectValue placeholder="Select key" />
                          </SelectTrigger>
                          <SelectContent>
                            {pods.map(
                              (pod) =>
                                isSignedPod(pod) &&
                                Object.entries(pod.entries).map(([key]) => (
                                  <SelectItem
                                    key={`${pod.id}:${key}`}
                                    value={`${pod.id}:${key}`}
                                  >
                                    {pod.id}.{key}
                                  </SelectItem>
                                ))
                            )}
                          </SelectContent>
                        </Select>
                        {isKeyValue(statement.secondArg.value) &&
                          statement.secondArg.value.podId &&
                          statement.secondArg.value.key && (
                            <span className="text-sm text-muted-foreground">
                              {(() => {
                                const pod = pods.find(
                                  (p) =>
                                    isKeyValue(statement.secondArg.value) &&
                                    p.id === statement.secondArg.value.podId
                                );
                                if (isSignedPod(pod)) {
                                  return (
                                    pod.entries[
                                      (statement.secondArg.value as KeyValue)
                                        .key
                                    ]?.toString() || "N/A"
                                  );
                                }
                                return "N/A";
                              })()}
                            </span>
                          )}
                      </>
                    )}

                    {statement.secondArg.type === "literal" && (
                      <div className="flex-1">
                        <TreeNodeEditor
                          node={
                            statement.secondArg.value || {
                              id: crypto.randomUUID(),
                              key: "",
                              type: "string",
                              value: ""
                            }
                          }
                          onUpdate={(node) =>
                            handleSecondArgLiteralChange(statement.id, node)
                          }
                        />
                      </div>
                    )}
                  </div>
                </div>
              </CardContent>
            </Card>
          ))}
        </div>
      </div>
    </div>
  );
}
