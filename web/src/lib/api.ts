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

  async createMainPod(): Promise<MainPod> {
    const { data } = await axiosInstance.post("/create-main-pod");
    return MainPodSchema.parse(data);
  }

  async deletePod(id: string): Promise<void> {
    await axiosInstance.post("/delete-pod", { id });
  }

  async importPod(pod: Pod): Promise<Pod> {
    const { data } = await axiosInstance.post("/import-pod", { pod });
    return PodSchema.parse(data);
  }

  async validateStatement(statement: Statement): Promise<boolean> {
    const { data } = await axiosInstance.post("/validate-statement", {
      statement
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
    mutationFn: api.createMainPod,
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
    mutationFn: (statement: Statement) => api.validateStatement(statement)
  });
}
