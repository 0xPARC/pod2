import axios from "axios";
import { useQuery, useMutation, useQueryClient } from "@tanstack/react-query";
import { z } from "zod";

// Zod schemas
const SignedPodSchema = z.object({
  entries: z.record(z.string(), z.any()),
  proof: z.string(),
  id: z.string(),
  pod_class: z.literal("Signed"),
  pod_type: z.literal("Mock")
});

const MainPodSchema = z.object({
  public_statements: z.array(z.any()),
  proof: z.string(),
  id: z.string(),
  pod_class: z.literal("Main"),
  pod_type: z.literal("Mock")
});

const PodSchema = z.discriminatedUnion("pod_class", [
  SignedPodSchema,
  MainPodSchema
]);

const StatementSchema = z.object({
  id: z.string()
});

// TypeScript types derived from schemas
export type SignedPod = z.infer<typeof SignedPodSchema>;
export type MainPod = z.infer<typeof MainPodSchema>;
export type Pod = z.infer<typeof PodSchema>;
export type Statement = z.infer<typeof StatementSchema>;

export type StatementType =
  | "Equal"
  | "NotEqual"
  | "Gt"
  | "Lt"
  | "Contains"
  | "NotContains";

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
  isValid?: boolean;
  isPending?: boolean;
}

export interface WildcardAnchoredKey {
  wildcardId:
    | {
        Concrete: [string, string]; // [PodClass, PodId]
      }
    | {
        Named: string;
      };
  key: string;
}

export interface FrontendWildcardStatement {
  Equal?:
    | [
        [{ Concrete: [string, string] } | { Named: string }, string],
        { Key: [[string, string], string] }
      ]
    | undefined;
  NotEqual?:
    | [
        [{ Concrete: [string, string] } | { Named: string }, string],
        { Key: [[string, string], string] }
      ]
    | undefined;
  Gt?:
    | [
        [{ Concrete: [string, string] } | { Named: string }, string],
        { Key: [[string, string], string] }
      ]
    | undefined;
  Lt?:
    | [
        [{ Concrete: [string, string] } | { Named: string }, string],
        { Key: [[string, string], string] }
      ]
    | undefined;
  Contains?:
    | [
        [{ Concrete: [string, string] } | { Named: string }, string],
        { Key: [[string, string], string] }
      ]
    | undefined;
  NotContains?:
    | [
        [{ Concrete: [string, string] } | { Named: string }, string],
        { Key: [[string, string], string] }
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
    keyValues: Record<string, any>
  ): Promise<SignedPod> {
    const { data } = await axiosInstance.post("/create-signed-pod", {
      signer,
      key_values: keyValues
    });
    return SignedPodSchema.parse(data);
  }

  async createMainPod(statements: EditorStatement[]): Promise<MainPod> {
    const frontendStatements = statements.map((s) => {
      // Convert EditorStatement to FrontendWildcardStatement
      const firstArg = [
        s.firstArg.wildcardId.type === "named"
          ? { Named: s.firstArg.wildcardId.value }
          : { Concrete: ["Signed", s.firstArg.wildcardId.value] },
        s.firstArg.key
      ];

      let secondArg;
      if (s.secondArg.type === "key") {
        secondArg = {
          Key: [["Signed", s.secondArg.value.podId], s.secondArg.value.key]
        };
      } else {
        // For literal values, we create a temporary key with the literal value
        secondArg = {
          Key: [
            ["Signed", String(s.secondArg.value.value)],
            s.secondArg.value.key
          ]
        };
      }

      // Create the statement object with the correct variant
      const statement: FrontendWildcardStatement = {
        [s.type]: [firstArg, secondArg]
      };

      return statement;
    });

    const { data } = await axiosInstance.post("/create-main-pod", {
      statements: frontendStatements
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
    const frontendStatements = statements.map((s) => {
      // Convert EditorStatement to FrontendWildcardStatement
      const firstArg = [
        s.firstArg.wildcardId.type === "named"
          ? { Named: s.firstArg.wildcardId.value }
          : { Concrete: ["Signed", s.firstArg.wildcardId.value] },
        s.firstArg.key
      ];

      let secondArg;
      if (s.secondArg.type === "key") {
        secondArg = {
          Key: [["Signed", s.secondArg.value.podId], s.secondArg.value.key]
        };
      } else {
        // For literal values, we create a temporary key with the literal value
        secondArg = {
          Key: [
            ["Signed", String(s.secondArg.value.value)],
            s.secondArg.value.key
          ]
        };
      }

      // Create the statement object with the correct variant
      const statement: FrontendWildcardStatement = {
        [s.type]: [firstArg, secondArg]
      };

      return statement;
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
      keyValues: Record<string, any>;
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
