import axios from "axios";
import { useQuery, useMutation, useQueryClient } from "@tanstack/react-query";
import { z } from "zod";

// Core value types
interface ValueType {
  String?: string;
  Int?: number;
  Bool?: boolean;
  Raw?: string;
  Array?: ValueType[];
  Set?: ValueType[];
  Dictionary?: Record<string, ValueType>;
}

const ValueSchema: z.ZodType<ValueType> = z.union([
  z.object({
    String: z.string()
  }),
  z.object({
    Int: z.number().int()
  }),
  z.object({
    Bool: z.boolean()
  }),
  z.object({
    Raw: z.string().regex(/^[0-9a-fA-F]{64}$/)
  }),
  z.object({
    Array: z.lazy(() => z.array(ValueSchema))
  }),
  z.object({
    Set: z.lazy(() => z.array(ValueSchema))
  }),
  z.object({
    Dictionary: z.lazy(() => z.record(z.string(), ValueSchema))
  })
]);

// Helper function to convert raw values to ValueSchema format
function convertToValueType(value: unknown): ValueType {
  if (typeof value === "string") {
    return { String: value };
  } else if (typeof value === "number" && Number.isInteger(value)) {
    return { Int: value };
  } else if (typeof value === "boolean") {
    return { Bool: value };
  } else if (Array.isArray(value)) {
    return { Array: value.map(convertToValueType) };
  } else if (value && typeof value === "object") {
    const dict: Record<string, ValueType> = {};
    for (const [k, v] of Object.entries(value)) {
      dict[k] = convertToValueType(v);
    }
    return { Dictionary: dict };
  }
  throw new Error(`Unsupported value type: ${typeof value}`);
}

// Remove or comment out the OriginSchema since it's no longer used
// const OriginSchema = z.object({
//   pod_class: z.enum(["Signed", "Main"]),
//   pod_id: z.string().regex(/^[0-9a-fA-F]{64}$/)
// });

// Remove or comment out the AnchoredKeySchema since it's no longer used
// const AnchoredKeySchema = z.object({
//   origin: OriginSchema,
//   key: z.string()
// });

const StatementArgSchema = z.union([
  z.object({
    Key: z.object({
      origin: z.object({
        pod_class: z.string(),
        pod_id: z.string()
      }),
      key: z.string()
    })
  }),
  z.object({
    Literal: ValueSchema
  })
]);

type StatementArg = z.infer<typeof StatementArgSchema>;

const PredicateSchema = z.discriminatedUnion("type", [
  z.object({
    type: z.literal("Native"),
    value: z.enum([
      "None",
      "ValueOf",
      "Equal",
      "NotEqual",
      "Gt",
      "Lt",
      "Contains",
      "NotContains",
      "SumOf",
      "ProductOf",
      "MaxOf"
    ])
  }),
  z.object({
    type: z.literal("BatchSelf"),
    value: z.number().int().nonnegative()
  }),
  z.object({
    type: z.literal("Custom"),
    value: z.tuple([
      z.object({
        name: z.string(),
        predicates: z.array(
          z.object({
            conjunction: z.boolean(),
            statements: z.array(
              z.tuple([
                z.any(), // Predicate
                z.array(z.any()) // StatementTmplArg array
              ])
            ),
            args_len: z.number().int().nonnegative()
          })
        )
      }),
      z.number().int().nonnegative()
    ])
  })
]);

const StatementSchema = z.object({
  predicate: PredicateSchema,
  args: z.array(StatementArgSchema)
});

const SignedPodSchema = z.object({
  entries: z.record(z.string(), z.unknown()).transform((entries) => {
    const converted: Record<string, ValueType> = {};
    for (const [key, value] of Object.entries(entries)) {
      converted[key] = convertToValueType(value);
    }
    return converted;
  }),
  proof: z.string(),
  id: z.string().regex(/^[0-9a-fA-F]{64}$/),
  pod_class: z.literal("Signed"),
  pod_type: z.literal("Mock")
});

const MainPodSchema = z.object({
  public_statements: z.array(StatementSchema),
  proof: z.string(),
  id: z.string().regex(/^[0-9a-fA-F]{64}$/),
  pod_class: z.literal("Main"),
  pod_type: z.literal("Mock")
});

const PodSchema = z.discriminatedUnion("pod_class", [
  SignedPodSchema,
  MainPodSchema
]);

// TypeScript types derived from schemas
export type SignedPod = z.infer<typeof SignedPodSchema>;
export type MainPod = z.infer<typeof MainPodSchema>;
export type Pod = z.infer<typeof PodSchema>;
export type Statement = z.infer<typeof StatementSchema>;

export type StatementType =
  | "None"
  | "ValueOf"
  | "Equal"
  | "NotEqual"
  | "Gt"
  | "Lt"
  | "Contains"
  | "NotContains"
  | "SumOf"
  | "ProductOf"
  | "MaxOf";

export interface TreeNode {
  id: string;
  key: string;
  type: string;
  value: string | number;
}

// Helper function to check if a value is a TreeNode
export function isTreeNode(value: any): value is TreeNode {
  return (
    typeof value === "object" &&
    value !== null &&
    "id" in value &&
    "key" in value &&
    "type" in value &&
    "value" in value
  );
}

export interface KeyValue {
  podId: string;
  podClass: string;
  key: string;
}

export function isKeyValue(value: any): value is KeyValue {
  return (
    typeof value === "object" &&
    value !== null &&
    "podId" in value &&
    "podClass" in value &&
    "key" in value
  );
}

export interface EditorStatement {
  id: string;
  type: StatementType;
  firstArg: {
    wildcardId: {
      type: "concrete" | "named";
      value: string;
    };
    key: string;
  };
  secondArg:
    | {
        type: "key";
        value: KeyValue;
      }
    | {
        type: "literal";
        value: TreeNode;
      };
  predicate?: {
    type: "Native";
    value: NativePredicate;
  };
  args?: Array<{
    type: "Key" | "Literal";
    value: KeyValue | TreeNode;
  }>;
  isValid?: boolean;
  isPending?: boolean;
}

export type NativePredicate =
  | "None"
  | "ValueOf"
  | "Equal"
  | "NotEqual"
  | "Gt"
  | "Lt"
  | "Contains"
  | "NotContains"
  | "SumOf"
  | "ProductOf"
  | "MaxOf";

export interface WildcardId {
  type: "Concrete" | "Named";
  value: { pod_class: "Signed" | "Main"; pod_id: string } | string;
}

export interface WildcardAnchoredKey {
  wildcard_id: WildcardId;
  key: string;
}

export interface FrontendWildcardStatement {
  Equal?:
    | [
        [
          WildcardAnchoredKey,
          {
            Key:
              | { origin: { pod_class: string; pod_id: string }; key: string }
              | {
                  Literal:
                    | { String: string }
                    | { Int: number }
                    | { Bool: boolean };
                };
          }
        ]
      ]
    | undefined;
  NotEqual?:
    | [
        [
          WildcardAnchoredKey,
          {
            Key:
              | { origin: { pod_class: string; pod_id: string }; key: string }
              | {
                  Literal:
                    | { String: string }
                    | { Int: number }
                    | { Bool: boolean };
                };
          }
        ]
      ]
    | undefined;
  Gt?:
    | [
        [
          WildcardAnchoredKey,
          {
            Key:
              | { origin: { pod_class: string; pod_id: string }; key: string }
              | {
                  Literal:
                    | { String: string }
                    | { Int: number }
                    | { Bool: boolean };
                };
          }
        ]
      ]
    | undefined;
  Lt?:
    | [
        [
          WildcardAnchoredKey,
          {
            Key:
              | { origin: { pod_class: string; pod_id: string }; key: string }
              | {
                  Literal:
                    | { String: string }
                    | { Int: number }
                    | { Bool: boolean };
                };
          }
        ]
      ]
    | undefined;
  Contains?:
    | [
        [
          WildcardAnchoredKey,
          {
            Key:
              | { origin: { pod_class: string; pod_id: string }; key: string }
              | {
                  Literal:
                    | { String: string }
                    | { Int: number }
                    | { Bool: boolean };
                };
          }
        ]
      ]
    | undefined;
  NotContains?:
    | [
        [
          WildcardAnchoredKey,
          {
            Key:
              | { origin: { pod_class: string; pod_id: string }; key: string }
              | {
                  Literal:
                    | { String: string }
                    | { Int: number }
                    | { Bool: boolean };
                };
          }
        ]
      ]
    | undefined;
}

const API_BASE = "http://localhost:3000/api";

const axiosInstance = axios.create({
  baseURL: API_BASE,
  headers: {
    "Content-Type": "application/json"
  }
});

class ApiClient {
  async listPods(): Promise<Pod[]> {
    const { data } = await axiosInstance.post("/list-pods");
    return z.array(PodSchema).parse(data);
  }

  async getPod(id: string): Promise<Pod> {
    const { data } = await axiosInstance.post("/get-pod", { id });
    return PodSchema.parse(data);
  }

  async createSignedPod(
    signer: string,
    keyValues: Record<string, unknown>
  ): Promise<SignedPod> {
    const { data } = await axiosInstance.post("/create-signed-pod", {
      signer,
      key_values: keyValues
    });
    return SignedPodSchema.parse(data);
  }

  async createMainPod(statements: EditorStatement[]): Promise<MainPod> {
    const transformedStatements = statements.map((statement) => {
      // Convert EditorStatement to FrontendWildcardStatement format
      const firstArg: WildcardAnchoredKey = {
        wildcard_id:
          statement.firstArg.wildcardId.type === "named"
            ? { type: "Named", value: statement.firstArg.wildcardId.value }
            : {
                type: "Concrete",
                value: {
                  pod_class: "Signed",
                  pod_id: statement.firstArg.wildcardId.value
                }
              },
        key: statement.firstArg.key
      };

      const secondArg =
        statement.secondArg.type === "key"
          ? {
              Key: {
                origin: {
                  pod_class: "Signed" as const,
                  pod_id: statement.secondArg.value.podId
                },
                key: statement.secondArg.value.key
              }
            }
          : {
              Literal: (() => {
                const val = statement.secondArg.value.value;
                if (typeof val === "string") {
                  return { String: val };
                } else if (typeof val === "number") {
                  return { Int: val };
                } else if (typeof val === "boolean") {
                  return { Bool: val };
                }
                throw new Error(`Unsupported literal type: ${typeof val}`);
              })()
            };

      // Create the statement object with the correct variant
      const validationStatement: FrontendWildcardStatement = {
        [statement.type]: [firstArg, secondArg]
      };

      return validationStatement;
    });

    const { data } = await axiosInstance.post("/create-main-pod", {
      statements: transformedStatements
    });
    return MainPodSchema.parse(data);
  }

  async deletePod(id: string): Promise<void> {
    await axiosInstance.post("/delete-pod", { id });
  }

  async importPod(pod: Pod): Promise<Pod> {
    const { data } = await axiosInstance.post("/import-pod", { pod });
    return PodSchema.parse(data);
  }

  async validateStatement(statement: EditorStatement): Promise<boolean> {
    const { data } = await axiosInstance.post("/validate-statement", {
      statement
    });
    return z.boolean().parse(data);
  }

  async validateStatements(statements: EditorStatement[]): Promise<boolean> {
    const frontendStatements = statements.map((statement) => {
      // Convert EditorStatement to FrontendWildcardStatement
      const firstArg: WildcardAnchoredKey = {
        wildcard_id:
          statement.firstArg.wildcardId.type === "named"
            ? { type: "Named", value: statement.firstArg.wildcardId.value }
            : {
                type: "Concrete",
                value: {
                  pod_class: "Signed",
                  pod_id: statement.firstArg.wildcardId.value
                }
              },
        key: statement.firstArg.key
      };

      const secondArg =
        statement.secondArg.type === "key"
          ? {
              Key: {
                origin: {
                  pod_class: "Signed" as const,
                  pod_id: statement.secondArg.value.podId
                },
                key: statement.secondArg.value.key
              }
            }
          : {
              Literal: (() => {
                const val = statement.secondArg.value.value;
                if (typeof val === "string") {
                  return { String: val };
                } else if (typeof val === "number") {
                  return { Int: val };
                } else if (typeof val === "boolean") {
                  return { Bool: val };
                }
                throw new Error(`Unsupported literal type: ${typeof val}`);
              })()
            };

      // Create the statement object with the correct variant
      const validationStatement: FrontendWildcardStatement = {
        [statement.type]: [firstArg, secondArg]
      };

      return validationStatement;
    });

    const { data } = await axiosInstance.post("/validate-statements", {
      statements: frontendStatements
    });
    return z.boolean().parse(data);
  }
}

export const api = new ApiClient();

// React Query hooks
export function useListPods() {
  return useQuery({
    queryKey: ["pods"],
    queryFn: () => api.listPods()
  });
}

export function useGetPod(id: string) {
  return useQuery({
    queryKey: ["pod", id],
    queryFn: () => api.getPod(id),
    enabled: !!id
  });
}

export function useCreateSignedPod() {
  const queryClient = useQueryClient();
  return useMutation({
    mutationFn: ({
      signer,
      keyValues
    }: {
      signer: string;
      keyValues: Record<string, unknown>;
    }) => api.createSignedPod(signer, keyValues),
    onSuccess: () => {
      queryClient.invalidateQueries({ queryKey: ["pods"] });
    }
  });
}

export function useCreateMainPod() {
  const queryClient = useQueryClient();
  return useMutation({
    mutationFn: (statements: EditorStatement[]) =>
      api.createMainPod(statements),
    onSuccess: () => {
      queryClient.invalidateQueries({ queryKey: ["pods"] });
    }
  });
}

export function useDeletePod() {
  const queryClient = useQueryClient();
  return useMutation({
    mutationFn: (id: string) => api.deletePod(id),
    onSuccess: () => {
      queryClient.invalidateQueries({ queryKey: ["pods"] });
    }
  });
}

export function useImportPod() {
  const queryClient = useQueryClient();
  return useMutation({
    mutationFn: (pod: Pod) => api.importPod(pod),
    onSuccess: () => {
      queryClient.invalidateQueries({ queryKey: ["pods"] });
    }
  });
}

export function useValidateStatement() {
  return useMutation({
    mutationFn: (statement: EditorStatement) => api.validateStatement(statement)
  });
}

export function isSignedPod(pod: Pod | undefined): pod is SignedPod {
  return pod?.pod_class === "Signed";
}

function shortenId(id: string): string {
  return id.slice(0, 6);
}

function formatValue(value: ValueType): string {
  const type = Object.keys(value)[0] as keyof ValueType;
  const val = value[type];

  switch (type) {
    case "Raw":
      return `Raw:${shortenId(val as string)}`;
    case "Array":
      return `[${(val as ValueType[]).map(formatValue).join(", ")}]`;
    case "Set":
      return `{${(val as ValueType[]).map(formatValue).join(", ")}}`;
    case "Dictionary":
      return `{${Object.entries(val as Record<string, ValueType>)
        .map(([k, v]) => `${k}: ${formatValue(v)}`)
        .join(", ")}}`;
    default:
      return `${type}:${val}`;
  }
}

function formatStatementArg(arg: StatementArg): string {
  if ("Key" in arg) {
    const { origin, key } = arg.Key;
    return `${origin.pod_class}:${shortenId(origin.pod_id)}.${key}`;
  } else if ("Literal" in arg) {
    return formatValue(arg.Literal);
  }
  return "";
}

export function formatStatement(statement: Statement): string {
  const { predicate, args } = statement;
  if (predicate.type !== "Native") return "";

  // Special handling for ValueOf which typically has one argument
  if (predicate.value === "ValueOf" && args.length > 0) {
    return `${predicate.value}(${formatStatementArg(args[0])})`;
  }

  // For other predicates that typically have two arguments
  const formattedArgs = args
    .map(formatStatementArg)
    .filter((arg) => arg !== "");
  return `${predicate.value}(${formattedArgs.join(", ")})`;
}
