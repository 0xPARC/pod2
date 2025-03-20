import axios from "axios";
import { useQuery, useMutation, useQueryClient } from "@tanstack/react-query";
import { z } from "zod";
import { TreeNode } from "./tree-node";
import {
  NativePredicateValue,
  PODValue,
  Statement,
  StatementArg,
  StatementSchema,
  ValueSchema
} from "./core-types";

export interface CreateSignedPodRequest {
  signer: string;
  key_values: Record<string, PODValue>;
}

export interface CreateSignedPodResponse {
  pod_id: string;
  statements: Statement[];
}

export interface GetPodResponse {
  pod_id: string;
  statements: Statement[];
}

export interface ListPodsResponse {
  pods: {
    pod_id: string;
    statements: Statement[];
  }[];
}

export interface ErrorResponse {
  error: string;
}

export function isAggregateType(type: NativePredicateValue): boolean {
  return type === "MaxOf" || type === "ProductOf" || type === "SumOf";
}

const SignedPodSchema = z.object({
  entries: z.record(z.string(), ValueSchema),
  proof: z.string(),
  id: z.string().regex(/^[0-9a-fA-F]{64}$/),
  pod_class: z.literal("Signed"),
  pod_type: z.literal("Mock"),
  nickname: z.string().optional()
});

const MainPodSchema = z.object({
  public_statements: z.array(StatementSchema),
  proof: z.string(),
  id: z.string().regex(/^[0-9a-fA-F]{64}$/),
  pod_class: z.literal("Main"),
  pod_type: z.literal("Mock"),
  nickname: z.string().optional()
});

const PodSchema = z.discriminatedUnion("pod_class", [
  SignedPodSchema,
  MainPodSchema
]);

const ValidatedStatementsSchema = z.array(
  z.tuple([
    StatementSchema,
    z.array(z.tuple([z.string(), z.array(StatementSchema), StatementSchema]))
  ])
);

// TypeScript types derived from schemas
export type SignedPod = z.infer<typeof SignedPodSchema>;
export type MainPod = z.infer<typeof MainPodSchema>;
export type Pod = z.infer<typeof PodSchema>;
export type ValidatedStatements = z.infer<typeof ValidatedStatementsSchema>;

// Helper function to check if a value is a TreeNode
export function isTreeNode(value: unknown): value is TreeNode {
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

export function isKeyValue(value: unknown): value is KeyValue {
  return (
    typeof value === "object" &&
    value !== null &&
    "podId" in value &&
    "podClass" in value &&
    "key" in value
  );
}

type KeyOrLiteral =
  | {
      type: "key";
      value: KeyValue;
    }
  | {
      type: "literal";
      value: PODValue;
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
              | { Literal: PODValue };
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
              | { Literal: PODValue };
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
              | { Literal: PODValue };
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
              | { Literal: PODValue };
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
              | { Literal: PODValue };
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
              | { Literal: PODValue };
          }
        ]
      ]
    | undefined;
}

interface WildcardStatementArg {
  Key?: {
    origin: {
      pod_class: "Signed";
      pod_id: string;
    };
    key: string;
  };
  Literal?: PODValue;
}

const API_BASE = "http://localhost:3000/api";

const axiosInstance = axios.create({
  baseURL: API_BASE,
  headers: {
    "Content-Type": "application/json"
  }
});

class ApiClient {
  baseUrl = API_BASE;

  async listPods(): Promise<Pod[]> {
    const { data } = await axiosInstance.post<Pod[]>("/list-pods");

    return z.array(PodSchema).parse(data);
  }

  async getPod(id: string): Promise<Pod> {
    const { data } = await axiosInstance.get<Pod>(`/get-pod/${id}`);
    return PodSchema.parse(data);
  }

  async createSignedPod(
    signer: string,
    keyValues: Record<string, unknown>,
    nickname?: string
  ): Promise<SignedPod> {
    const { data } = await axiosInstance.post<SignedPod>("/create-signed-pod", {
      signer,
      key_values: keyValues,
      nickname
    });
    return SignedPodSchema.parse(data);
  }

  async createMainPod(
    statements: EditorStatement[],
    nickname?: string
  ): Promise<MainPod> {
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

      const secondArg = transformArg(statement.secondArg);

      // For three-argument statements, include the third argument
      if (isAggregateType(statement.type) && statement.thirdArg) {
        const thirdArg = transformArg(statement.thirdArg);
        return {
          [statement.type]: [firstArg, secondArg, thirdArg]
        };
      }

      // For two-argument statements
      return {
        [statement.type]: [firstArg, secondArg]
      };
    });

    const { data } = await axiosInstance.post<MainPod>("/create-main-pod", {
      statements: transformedStatements,
      nickname
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

  async exportPod(id: string): Promise<Pod> {
    const { data } = await axiosInstance.get(`/export/${id}`);
    return PodSchema.parse(data);
  }

  async updatePodNickname(id: string, nickname: string | null): Promise<Pod> {
    const { data } = await axiosInstance.post("/update-pod-nickname", {
      id,
      nickname
    });
    return PodSchema.parse(data);
  }

  async validateStatements(
    statements: EditorStatement[]
  ): Promise<ValidatedStatements> {
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

      const secondArg = transformArg(statement.secondArg);

      // For three-argument statements, include the third argument
      if (isAggregateType(statement.type) && statement.thirdArg) {
        const thirdArg = transformArg(statement.thirdArg);
        return {
          [statement.type]: [firstArg, secondArg, thirdArg]
        };
      }

      // For two-argument statements
      return {
        [statement.type]: [firstArg, secondArg]
      };
    });

    const { data } = await axiosInstance.post("/validate-statements", {
      statements: frontendStatements
    });
    return ValidatedStatementsSchema.parse(data);
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
    mutationFn: (statements: EditorStatement[], nickname?: string) =>
      api.createMainPod(statements, nickname),
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

export function isSignedPod(pod: Pod | undefined): pod is SignedPod {
  return pod?.pod_class === "Signed";
}

function shortenId(id: string): string {
  return id.slice(0, 6);
}

function formatValue(value: PODValue): string {
  if (typeof value === "string") {
    return value;
  } else if (typeof value === "boolean") {
    return value.toString();
  } else if ("Set" in value) {
    const setValues = value.Set[0];
    if (Array.isArray(setValues)) {
      return `{${setValues.map(formatValue).join(", ")}}`;
    }
    return `{${formatValue(setValues)}}`;
  } else if ("Dictionary" in value) {
    return `{${Object.entries(value.Dictionary)
      .map(([k, v]) => `${k}: ${formatValue(v)}`)
      .join(", ")}}`;
  } else if ("Int" in value) {
    return value.Int;
  } else if ("Raw" in value) {
    return value.Raw;
  } else if (Array.isArray(value)) {
    return `[${value.map(formatValue).join(", ")}]`;
  }
  throw new Error(`Unsupported value type: ${typeof value}`);
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

function transformArg(arg: {
  type: "key" | "literal";
  value: KeyValue | PODValue;
}): WildcardStatementArg {
  if (arg.type === "key" && isKeyValue(arg.value)) {
    return {
      Key: {
        origin: {
          pod_class: "Signed",
          pod_id: arg.value.podId
        },
        key: arg.value.key
      }
    };
  } else {
    return { Literal: arg.value as PODValue };
  }
}
