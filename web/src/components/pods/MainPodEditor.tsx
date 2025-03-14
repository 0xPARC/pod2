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
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { api, Pod, Statement as ApiStatement } from "@/lib/api";
import { TreeNodeEditor, TreeNode, ValueType } from "./CreateSignedPodEditor";
import { Switch } from "@/components/ui/switch";
import { Label } from "@/components/ui/label";
import { useDebounce } from "@/lib/hooks/useDebounce";

// Define the available statement types based on the documentation
export type StatementType =
  | "Equal"
  | "NotEqual"
  | "Gt"
  | "Lt"
  | "GEq"
  | "LEq"
  | "SumOf"
  | "ProductOf"
  | "MaxOf";

export interface AnchoredKey {
  podId: string;
  podClass: "Signed" | "Main";
  key: string;
}

export interface Statement {
  id: string;
  type: StatementType;
  firstArg: AnchoredKey;
  secondArgType: "anchoredKey" | "literal";
  secondArgAnchoredKey?: AnchoredKey;
  secondArgLiteral?: TreeNode;
  isValid?: boolean;
  isPending?: boolean;
}

// Helper function to check if a pod is a SignedPod
function isSignedPod(pod: Pod | undefined): pod is {
  pod_class: "Signed";
  entries: Record<string, any>;
  proof: string;
  id: string;
  pod_type: "Mock";
} {
  return pod?.pod_class === "Signed";
}

export function MainPodEditor() {
  const [statements, setStatements] = useState<Statement[]>([]);
  const [pods, setPods] = useState<Pod[]>([]);
  const debouncedStatements = useDebounce(statements, 500);

  // Load available PODs
  useEffect(() => {
    api.listPods().then(setPods);
  }, []);

  // Validate statements when they change
  useEffect(() => {
    const validateStatements = async () => {
      // Skip validation if no statements
      if (debouncedStatements.length === 0) {
        return;
      }

      // Set all statements to pending
      setStatements((prev) => prev.map((s) => ({ ...s, isPending: true })));

      try {
        // Convert frontend statements to API statements
        const apiStatements: ApiStatement[] = debouncedStatements
          .filter((s) => s.firstArg.podId && s.firstArg.key)
          .map((s) => ({
            id: s.id,
            type: s.type,
            firstArg: s.firstArg,
            secondArgType: s.secondArgType,
            secondArgAnchoredKey: s.secondArgAnchoredKey,
            secondArgLiteral: s.secondArgLiteral
          }));

        // Validate all statements together
        const isValid = await api.validateStatements(apiStatements);

        // Update validation state for all statements
        setStatements((prev) =>
          prev.map((s) => ({ ...s, isValid, isPending: false }))
        );
      } catch (error) {
        // On error, mark all statements as invalid
        setStatements((prev) =>
          prev.map((s) => ({ ...s, isValid: false, isPending: false }))
        );
      }
    };

    validateStatements();
  }, [debouncedStatements]);

  function handleAddStatement() {
    const newStatement: Statement = {
      id: crypto.randomUUID(),
      type: "Equal",
      firstArg: { podId: "", podClass: "Signed", key: "" },
      secondArgType: "anchoredKey",
      secondArgAnchoredKey: { podId: "", podClass: "Signed", key: "" }
    };
    setStatements([...statements, newStatement]);
  }

  function handleDeleteStatement(id: string) {
    setStatements(statements.filter((s) => s.id !== id));
  }

  function handleStatementTypeChange(id: string, type: StatementType) {
    setStatements(statements.map((s) => (s.id === id ? { ...s, type } : s)));
  }

  function handleFirstArgChange(id: string, arg: AnchoredKey) {
    setStatements(
      statements.map((s) => (s.id === id ? { ...s, firstArg: arg } : s))
    );
  }

  function handleSecondArgTypeChange(
    id: string,
    type: "anchoredKey" | "literal"
  ) {
    setStatements(
      statements.map((s) =>
        s.id === id
          ? {
              ...s,
              secondArgType: type,
              secondArgAnchoredKey:
                type === "anchoredKey"
                  ? { podId: "", podClass: "Signed", key: "" }
                  : undefined,
              secondArgLiteral:
                type === "literal"
                  ? {
                      id: crypto.randomUUID(),
                      key: "",
                      type: "string",
                      value: ""
                    }
                  : undefined
            }
          : s
      )
    );
  }

  function handleSecondArgAnchoredKeyChange(id: string, arg: AnchoredKey) {
    setStatements(
      statements.map((s) =>
        s.id === id ? { ...s, secondArgAnchoredKey: arg } : s
      )
    );
  }

  function handleSecondArgLiteralChange(id: string, node: TreeNode) {
    setStatements(
      statements.map((s) =>
        s.id === id ? { ...s, secondArgLiteral: node } : s
      )
    );
  }

  return (
    <div className="space-y-6">
      <div className="flex items-center justify-between">
        <h2 className="text-2xl font-bold">Main POD Editor</h2>
        <Button onClick={handleAddStatement}>
          <Plus className="w-4 h-4 mr-2" />
          Add Statement
        </Button>
      </div>

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
                        <SelectItem value="GEq">GEq</SelectItem>
                        <SelectItem value="LEq">LEq</SelectItem>
                        <SelectItem value="SumOf">SumOf</SelectItem>
                        <SelectItem value="ProductOf">ProductOf</SelectItem>
                        <SelectItem value="MaxOf">MaxOf</SelectItem>
                      </SelectContent>
                    </Select>
                  </div>
                  <div className="flex items-center gap-2">
                    {statement.isPending ? (
                      <Loader2 className="w-4 h-4 animate-spin text-muted-foreground" />
                    ) : statement.isValid ? (
                      <CheckCircle2 className="w-4 h-4 text-green-500" />
                    ) : statement.isValid === false ? (
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
                    <span className="text-sm font-medium">First Argument</span>
                  </div>
                  <Select
                    value={`${statement.firstArg.podId}:${statement.firstArg.key}`}
                    onValueChange={(value) => {
                      const [podId, key] = value.split(":");
                      const pod = pods.find((p) => p.id === podId);
                      if (pod) {
                        handleFirstArgChange(statement.id, {
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
                          Object.entries(pod.entries).map(([key, value]) => (
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
                  {statement.firstArg.podId && statement.firstArg.key && (
                    <span className="text-sm text-muted-foreground">
                      {(() => {
                        const pod = pods.find(
                          (p) => p.id === statement.firstArg.podId
                        );
                        if (isSignedPod(pod)) {
                          return (
                            pod.entries[statement.firstArg.key]?.toString() ||
                            "N/A"
                          );
                        }
                        return "N/A";
                      })()}
                    </span>
                  )}
                </div>

                <div className="flex items-center gap-4">
                  <div className="flex items-center gap-2">
                    <span className="text-sm font-medium">Second Argument</span>
                  </div>
                  <Select
                    value={statement.secondArgType}
                    onValueChange={(value) =>
                      handleSecondArgTypeChange(
                        statement.id,
                        value as "anchoredKey" | "literal"
                      )
                    }
                  >
                    <SelectTrigger className="w-[180px]">
                      <SelectValue placeholder="Select type" />
                    </SelectTrigger>
                    <SelectContent>
                      <SelectItem value="anchoredKey">Anchored Key</SelectItem>
                      <SelectItem value="literal">Literal Value</SelectItem>
                    </SelectContent>
                  </Select>

                  {statement.secondArgType === "anchoredKey" && (
                    <>
                      <Select
                        value={`${statement.secondArgAnchoredKey?.podId}:${statement.secondArgAnchoredKey?.key}`}
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
                              Object.entries(pod.entries).map(
                                ([key, value]) => (
                                  <SelectItem
                                    key={`${pod.id}:${key}`}
                                    value={`${pod.id}:${key}`}
                                  >
                                    {pod.id}.{key}
                                  </SelectItem>
                                )
                              )
                          )}
                        </SelectContent>
                      </Select>
                      {statement.secondArgAnchoredKey?.podId &&
                        statement.secondArgAnchoredKey?.key && (
                          <span className="text-sm text-muted-foreground">
                            {(() => {
                              const pod = pods.find(
                                (p) =>
                                  p.id === statement.secondArgAnchoredKey?.podId
                              );
                              if (isSignedPod(pod)) {
                                return (
                                  pod.entries[
                                    statement.secondArgAnchoredKey?.key
                                  ]?.toString() || "N/A"
                                );
                              }
                              return "N/A";
                            })()}
                          </span>
                        )}
                    </>
                  )}

                  {statement.secondArgType === "literal" && (
                    <div className="flex-1">
                      <TreeNodeEditor
                        node={
                          statement.secondArgLiteral || {
                            id: crypto.randomUUID(),
                            key: "",
                            type: "string",
                            value: ""
                          }
                        }
                        onUpdate={(node) =>
                          handleSecondArgLiteralChange(statement.id, node)
                        }
                        onDelete={() => {}}
                        onAddChild={() => {}}
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
  );
}
