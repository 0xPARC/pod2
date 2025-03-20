import { useEffect, useState } from "react";
import { api, Pod } from "@/lib/api";
import {
  Table,
  TableBody,
  TableCell,
  TableHead,
  TableHeader,
  TableRow
} from "@/components/ui/table";
import { Button } from "@/components/ui/button";
import {
  TrashIcon,
  ChevronDownIcon,
  ChevronRightIcon,
  DownloadIcon,
  CopyIcon
} from "lucide-react";
import { ImportPodDialog } from "./ImportPodDialog";
import { toast } from "sonner";
import { useNavigate } from "@tanstack/react-router";
import { formatStatement } from "@/lib/core-types";
import {
  Tooltip,
  TooltipContent,
  TooltipProvider,
  TooltipTrigger
} from "@/components/ui/tooltip";
import { EditableNickname } from "./EditableNickname";

interface ApiError {
  response?: {
    data?: {
      error?: string;
    };
  };
  message: string;
}

export function PodList() {
  const navigate = useNavigate();
  const [pods, setPods] = useState<Pod[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [expandedPods, setExpandedPods] = useState<Set<string>>(new Set());

  useEffect(() => {
    loadPods();
  }, []);

  async function loadPods() {
    try {
      setLoading(true);
      const pods = await api.listPods();
      setPods(pods);
      setError(null);
    } catch (err) {
      setError("Failed to load PODs");
      console.error(err);
      toast.error("Failed to load PODs");
    } finally {
      setLoading(false);
    }
  }

  async function handleDelete(id: string) {
    try {
      await api.deletePod(id);
      await loadPods(); // Refresh the list
      toast.success("POD deleted successfully");
    } catch (err: unknown) {
      console.error(err);
      const apiError = err as ApiError;
      const errorMessage =
        apiError.response?.data?.error || "Failed to delete POD";
      toast.error(errorMessage);
    }
  }

  async function handleExport(id: string) {
    try {
      // Open the export URL directly in a new tab
      window.open(`${api.baseUrl}/export/${id}`, "_blank");
    } catch (err: unknown) {
      console.error(err);
      const apiError = err as ApiError;
      const errorMessage =
        apiError.response?.data?.error || "Failed to export POD";
      toast.error(errorMessage);
    }
  }

  async function handleCopyId(id: string) {
    try {
      await navigator.clipboard.writeText(id);
      toast.success("POD ID copied to clipboard");
    } catch (err) {
      console.error("Failed to copy:", err);
      toast.error("Failed to copy POD ID");
    }
  }

  function toggleExpand(id: string) {
    const newExpanded = new Set(expandedPods);
    if (newExpanded.has(id)) {
      newExpanded.delete(id);
    } else {
      newExpanded.add(id);
    }
    setExpandedPods(newExpanded);
  }

  if (loading) return <div>Loading...</div>;
  if (error) return <div className="text-red-500">{error}</div>;

  return (
    <div className="container mx-auto py-8">
      <div className="flex justify-between items-center mb-6">
        <h1 className="text-2xl font-bold">PODs</h1>
        <div className="space-x-2 flex items-center">
          <ImportPodDialog onPodImported={loadPods} />
          <Button
            variant="outline"
            onClick={() => navigate({ to: "/create/main" })}
          >
            Create Main POD
          </Button>
          <Button
            variant="outline"
            onClick={() => navigate({ to: "/create/signed" })}
          >
            Create Signed POD
          </Button>
        </div>
      </div>

      <Table>
        <TableHeader>
          <TableRow>
            <TableHead className="w-12"></TableHead>
            <TableHead>ID</TableHead>
            <TableHead>Nickname</TableHead>
            <TableHead>Type</TableHead>
            <TableHead>Details</TableHead>
            <TableHead className="w-24">Actions</TableHead>
          </TableRow>
        </TableHeader>
        <TableBody>
          {pods.map((pod) => (
            <>
              <TableRow key={pod.id}>
                <TableCell>
                  <Button
                    variant="ghost"
                    size="icon"
                    onClick={() => toggleExpand(pod.id)}
                  >
                    {expandedPods.has(pod.id) ? (
                      <ChevronDownIcon className="w-4 h-4" />
                    ) : (
                      <ChevronRightIcon className="w-4 h-4" />
                    )}
                  </Button>
                </TableCell>
                <TableCell>
                  <div className="flex items-center space-x-2">
                    <TooltipProvider>
                      <Tooltip>
                        <TooltipTrigger asChild>
                          <span className="font-mono">
                            {pod.id.slice(0, 12) + "..."}
                          </span>
                        </TooltipTrigger>
                        <TooltipContent>
                          <p className="font-mono">{pod.id}</p>
                        </TooltipContent>
                      </Tooltip>
                    </TooltipProvider>
                    <Button
                      variant="ghost"
                      size="icon"
                      onClick={() => handleCopyId(pod.id)}
                    >
                      <CopyIcon className="w-4 h-4" />
                    </Button>
                  </div>
                </TableCell>
                <TableCell>
                  <EditableNickname
                    id={pod.id}
                    initialNickname={pod.nickname}
                    onUpdate={loadPods}
                  />
                </TableCell>
                <TableCell>{pod.pod_class}</TableCell>
                <TableCell>
                  {pod.pod_class === "Signed" ? (
                    <div>
                      <div className="text-sm text-gray-500">
                        {Object.keys(pod.entries).length} key-value pairs
                      </div>
                    </div>
                  ) : (
                    <div>
                      <div className="text-sm text-gray-500">
                        {pod.public_statements.length} public statements
                      </div>
                    </div>
                  )}
                </TableCell>
                <TableCell>
                  <div className="flex space-x-2">
                    <Button
                      variant="ghost"
                      size="icon"
                      onClick={() => handleExport(pod.id)}
                    >
                      <DownloadIcon className="w-4 h-4" />
                    </Button>
                    <Button
                      variant="ghost"
                      size="icon"
                      onClick={() => handleDelete(pod.id)}
                    >
                      <TrashIcon className="w-4 h-4" />
                    </Button>
                  </div>
                </TableCell>
              </TableRow>
              {expandedPods.has(pod.id) && (
                <TableRow>
                  <TableCell colSpan={5}>
                    <div className="bg-gray-50 p-4 rounded-lg">
                      <div className="space-y-2">
                        {pod.pod_class === "Signed"
                          ? // Signed Pod expanded view
                            Object.entries(pod.entries)
                              .sort(([keyA], [keyB]) =>
                                keyA.localeCompare(keyB)
                              )
                              .map(([key, value]) => (
                                <div
                                  key={key}
                                  className="flex items-center space-x-2"
                                >
                                  <span className="font-medium">{key}:</span>
                                  <span className="text-gray-600">
                                    {JSON.stringify(value)}
                                  </span>
                                </div>
                              ))
                          : // Main Pod expanded view
                            pod.public_statements.map((statement, index) => (
                              <div
                                key={index}
                                className="flex items-start space-x-2"
                              >
                                <span className="font-medium">
                                  Statement {index + 1}:
                                </span>
                                <span className="font-mono text-gray-600">
                                  {formatStatement({
                                    ...statement,
                                    args: statement.args.map((arg) => {
                                      if ("Key" in arg) {
                                        return {
                                          ...arg,
                                          Key: {
                                            ...arg.Key,
                                            origin: {
                                              ...arg.Key.origin,
                                              pod_class: arg.Key.origin
                                                .pod_class as "Signed" | "Main"
                                            }
                                          }
                                        };
                                      }
                                      return arg;
                                    })
                                  })}
                                </span>
                              </div>
                            ))}
                      </div>
                    </div>
                  </TableCell>
                </TableRow>
              )}
            </>
          ))}
          {pods.length === 0 && (
            <TableRow>
              <TableCell colSpan={5} className="text-center py-8">
                No PODs found. Create one to get started.
              </TableCell>
            </TableRow>
          )}
        </TableBody>
      </Table>
    </div>
  );
}
