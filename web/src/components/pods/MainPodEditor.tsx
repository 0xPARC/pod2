import { useState, useEffect } from "react";
import { Button } from "@/components/ui/button";
import {
  Select,
  SelectContent,
  SelectItem,
  SelectSeparator,
  SelectTrigger,
  SelectValue
} from "@/components/ui/select";
import { Plus, Trash2, CheckCircle2, XCircle, Loader2 } from "lucide-react";
import { Card, CardContent } from "@/components/ui/card";
import { api, Pod, isSignedPod, KeyValue, isKeyValue } from "@/lib/api";
import { useDebounce } from "@/lib/hooks/useDebounce";
import { useNavigate } from "@tanstack/react-router";
import { toast } from "sonner";
import { Input } from "@/components/ui/input";
import { TreeNode, ValueType } from "@/lib/tree-node";
import { PODValue } from "@/lib/core-types";
import { formatValue, NativePredicateValue } from "@/lib/core-types";
import { TreeNodeEditor } from "./TreeNodeEditor";

type KeyOrLiteral =
  | {
      type: "key";
      value: KeyValue;
    }
  | {
      type: "literal";
      value: PODValue | null;
    };

export interface EditorStatement {
  id: string;
  type: NativePredicateValue;
  firstArg: {
    wildcardId: { type: "concrete" | "named"; value: string };
    key: string;
  };
  secondArg: KeyOrLiteral;
  thirdArg?: KeyOrLiteral;
}

function truncatePodId(id: string): string {
  return id.slice(0, 8);
}

interface ValidationState {
  isValid: boolean;
  isPending: boolean;
}

export function MainPodEditor() {
  const [statements, setStatements] = useState<EditorStatement[]>([]);
  const [nickname, setNickname] = useState<string>("");
  const [pods, setPods] = useState<Pod[]>([]);
  const [validationState, setValidationState] = useState<ValidationState>({
    isValid: false,
    isPending: false
  });
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
      if (!(statement.secondArg.value.podId && statement.secondArg.value.key)) {
        return false;
      }
    } else {
      if (statement.secondArg.value === null) {
        return false;
      }
    }

    // Check third argument for three-arg statements
    if (isThreeArgStatement(statement.type)) {
      if (!statement.thirdArg) return false;
      if (statement.thirdArg.type === "key") {
        return !!(
          statement.thirdArg.value.podId && statement.thirdArg.value.key
        );
      } else {
        return statement.thirdArg.value !== null;
      }
    }

    return true;
  }

  function isThreeArgStatement(type: NativePredicateValue): boolean {
    return type === "MaxOf" || type === "ProductOf" || type === "SumOf";
  }

  // Validate statements when they change
  useEffect(() => {
    setValidationState({ isValid: false, isPending: true });
    const validateStatements = async () => {
      if (debouncedStatements.length === 0) return;

      // Only validate if all statements are complete
      if (!debouncedStatements.every(isStatementComplete)) return;

      try {
        const result = await api.validateStatements(debouncedStatements);
        setValidationState({ isPending: false, isValid: result.length > 0 });
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

  function handleStatementTypeChange(id: string, type: NativePredicateValue) {
    setStatements(
      statements.map((s) => {
        if (s.id === id) {
          const updatedStatement = { ...s, type };
          // Initialize third argument for three-argument statements
          if (isThreeArgStatement(type) && !updatedStatement.thirdArg) {
            updatedStatement.thirdArg = {
              type: "key",
              value: { podId: "", podClass: "Signed", key: "" }
            };
          }
          return updatedStatement;
        }
        return s;
      })
    );
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
                      value: null
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

  function treeNodeToPODValue(node: TreeNode): PODValue {
    switch (node.type) {
      case ValueType.String:
        return node.value as string;
      case ValueType.Int:
        return { Int: node.value as string };
      case ValueType.Bool:
        return node.value ? true : false;
      case ValueType.Raw:
        return { Raw: node.value as string };
      case ValueType.Array:
        return (node.children || []).map((child) => treeNodeToPODValue(child));
      case ValueType.Set:
        return {
          Set: (node.children || []).map((child) => treeNodeToPODValue(child))
        };
      case ValueType.Dictionary:
        return {
          Dictionary: Object.fromEntries(
            (node.children || []).map((child) => [
              child.key,
              treeNodeToPODValue(child)
            ])
          )
        };
    }
  }

  function podValueToTreeNode(value: PODValue | null): TreeNode {
    if (value === null) {
      return {
        id: crypto.randomUUID(),
        key: "",
        type: ValueType.String,
        value: ""
      };
    }

    if (typeof value === "string") {
      return {
        id: crypto.randomUUID(),
        key: "",
        type: ValueType.String,
        value
      };
    }

    if (typeof value === "boolean") {
      return {
        id: crypto.randomUUID(),
        key: "",
        type: ValueType.Bool,
        value
      };
    }

    if ("Int" in value) {
      return {
        id: crypto.randomUUID(),
        key: "",
        type: ValueType.Int,
        value: value.Int
      };
    }

    if ("Raw" in value) {
      return {
        id: crypto.randomUUID(),
        key: "",
        type: ValueType.Raw,
        value: value.Raw
      };
    }

    if ("Set" in value) {
      return {
        id: crypto.randomUUID(),
        key: "",
        type: ValueType.Set,
        value: { Set: value.Set },
        children: value.Set.map((child) => podValueToTreeNode(child))
      };
    }

    if ("Dictionary" in value) {
      return {
        id: crypto.randomUUID(),
        key: "",
        type: ValueType.Dictionary,
        value: { Dictionary: value.Dictionary },
        children: Object.entries(value.Dictionary).map(([key, child]) => ({
          ...podValueToTreeNode(child),
          key
        }))
      };
    }

    if (Array.isArray(value)) {
      return {
        id: crypto.randomUUID(),
        key: "",
        type: ValueType.Array,
        value: value,
        children: value.map((child) => podValueToTreeNode(child))
      };
    }

    throw new Error(`Unsupported PODValue type: ${typeof value}`);
  }

  function handleSecondArgLiteralChange(id: string, node: TreeNode) {
    console.log({
      id,
      node,
      podValue: treeNodeToPODValue(node)
    });
    setStatements(
      statements.map((s) =>
        s.id === id
          ? {
              ...s,
              secondArg: {
                type: "literal",
                value: treeNodeToPODValue(node)
              }
            }
          : s
      )
    );
  }

  function handleThirdArgTypeChange(id: string, type: "key" | "literal") {
    setStatements(
      statements.map((s) =>
        s.id === id
          ? {
              ...s,
              thirdArg:
                type === "key"
                  ? {
                      type: "key",
                      value: { podId: "", podClass: "Signed", key: "" }
                    }
                  : {
                      type: "literal",
                      value: null
                    }
            }
          : s
      )
    );
  }

  function handleThirdArgAnchoredKeyChange(id: string, arg: KeyValue) {
    setStatements(
      statements.map((s) =>
        s.id === id && s.thirdArg?.type === "key"
          ? {
              ...s,
              thirdArg: {
                type: "key",
                value: arg
              }
            }
          : s
      )
    );
  }

  function handleThirdArgLiteralChange(id: string, node: TreeNode) {
    setStatements(
      statements.map((s) =>
        s.id === id && s.thirdArg?.type === "literal"
          ? {
              ...s,
              thirdArg: {
                type: "literal",
                value: treeNodeToPODValue(node)
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
                              value as NativePredicateValue
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
                            <SelectItem value="MaxOf">MaxOf</SelectItem>
                            <SelectItem value="ProductOf">ProductOf</SelectItem>
                            <SelectItem value="SumOf">SumOf</SelectItem>
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
                            (pod, index) =>
                              isSignedPod(pod) && [
                                <>
                                  {index > 0 && <SelectSeparator />}
                                  <div className="text-sm py-1 px-2 bg-muted text-muted-foreground">
                                    {truncatePodId(pod.id)}{" "}
                                    {pod.nickname && `(${pod.nickname})`}
                                  </div>
                                </>,
                                ...Object.entries(pod.entries).map(
                                  ([key, value]) => (
                                    <SelectItem
                                      key={`${pod.id}:${key}`}
                                      value={`${pod.id}:${key}`}
                                    >
                                      {key} = {formatValue(value)}
                                    </SelectItem>
                                  )
                                )
                              ]
                          )}
                        </SelectContent>
                      </Select>
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
                                (pod, index) =>
                                  isSignedPod(pod) && [
                                    <>
                                      {index > 0 && <SelectSeparator />}
                                      <div className="text-sm py-1 px-2 bg-muted text-muted-foreground">
                                        {truncatePodId(pod.id)}{" "}
                                        {pod.nickname && `(${pod.nickname})`}
                                      </div>
                                    </>,
                                    ...Object.entries(pod.entries).map(
                                      ([key, value]) => (
                                        <SelectItem
                                          key={`${pod.id}:${key}`}
                                          value={`${pod.id}:${key}`}
                                        >
                                          {key} = {formatValue(value)}
                                        </SelectItem>
                                      )
                                    )
                                  ]
                              )}
                            </SelectContent>
                          </Select>
                        </>
                      )}

                      {statement.secondArg.type === "literal" && (
                        <div className="flex-1">
                          <TreeNodeEditor
                            hideDelete={true}
                            hideKey={true}
                            node={podValueToTreeNode(statement.secondArg.value)}
                            onUpdate={(node) =>
                              handleSecondArgLiteralChange(statement.id, node)
                            }
                            onDelete={() => {}}
                            onAddChild={() => {
                              /* @TODO */
                            }}
                          />
                        </div>
                      )}
                    </div>

                    {isThreeArgStatement(statement.type) && (
                      <div className="flex items-center gap-4">
                        <div className="flex items-center gap-2">
                          <span className="text-sm font-medium">
                            Third Argument
                          </span>
                        </div>
                        <Select
                          value={statement.thirdArg?.type || "key"}
                          onValueChange={(value) =>
                            handleThirdArgTypeChange(
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
                            <SelectItem value="literal">
                              Literal Value
                            </SelectItem>
                          </SelectContent>
                        </Select>

                        {statement.thirdArg?.type === "key" && (
                          <>
                            <Select
                              value={
                                statement.thirdArg.type === "key"
                                  ? `${statement.thirdArg.value.podId}:${statement.thirdArg.value.key}`
                                  : ""
                              }
                              onValueChange={(value) => {
                                const [podId, key] = value.split(":");
                                const pod = pods.find((p) => p.id === podId);
                                if (pod) {
                                  handleThirdArgAnchoredKeyChange(
                                    statement.id,
                                    {
                                      podId,
                                      podClass: pod.pod_class,
                                      key
                                    }
                                  );
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
                                          {truncatePodId(pod.id)}.{key} ={" "}
                                          {formatValue(value)}
                                        </SelectItem>
                                      )
                                    )
                                )}
                              </SelectContent>
                            </Select>
                          </>
                        )}

                        {statement.thirdArg?.type === "literal" && (
                          <div className="flex-1">
                            <TreeNodeEditor
                              hideDelete={true}
                              hideKey={true}
                              node={podValueToTreeNode(
                                statement.thirdArg.value
                              )}
                              onUpdate={(node) =>
                                handleThirdArgLiteralChange(statement.id, node)
                              }
                              onDelete={() => {}}
                              onAddChild={() => {
                                /* @TODO */
                              }}
                            />
                          </div>
                        )}
                      </div>
                    )}
                  </div>
                </CardContent>
              </Card>
            ))}
          </div>
        </div>
      </div>
    </div>
  );
}
