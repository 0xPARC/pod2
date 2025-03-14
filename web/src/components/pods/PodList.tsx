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
import { TrashIcon, ChevronDownIcon, ChevronRightIcon } from "lucide-react";
import { CreatePodDialog } from "./CreatePodDialog";
import { ImportPodDialog } from "./ImportPodDialog";
import { toast } from "sonner";

export function PodList() {
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
    } catch (err: any) {
      console.error(err);
      const errorMessage = err.response?.data?.error || "Failed to delete POD";
      toast.error(errorMessage);
    }
  }

  function toggleExpand(proof: string) {
    const newExpanded = new Set(expandedPods);
    if (newExpanded.has(proof)) {
      newExpanded.delete(proof);
    } else {
      newExpanded.add(proof);
    }
    setExpandedPods(newExpanded);
  }

  if (loading) return <div>Loading...</div>;
  if (error) return <div className="text-red-500">{error}</div>;

  return (
    <div className="container mx-auto py-8">
      <div className="flex justify-between items-center mb-6">
        <h1 className="text-2xl font-bold">PODs</h1>
        <div className="space-x-2">
          <ImportPodDialog onPodImported={loadPods} />
          <CreatePodDialog onPodCreated={loadPods} />
        </div>
      </div>

      <Table>
        <TableHeader>
          <TableRow>
            <TableHead className="w-12"></TableHead>
            <TableHead>ID</TableHead>
            <TableHead>Type</TableHead>
            <TableHead>Details</TableHead>
            <TableHead className="w-24">Actions</TableHead>
          </TableRow>
        </TableHeader>
        <TableBody>
          {pods.map((pod) => (
            <>
              <TableRow key={pod.proof}>
                <TableCell>
                  {pod.pod_class === "Signed" && (
                    <Button
                      variant="ghost"
                      size="icon"
                      onClick={() => toggleExpand(pod.proof)}
                    >
                      {expandedPods.has(pod.proof) ? (
                        <ChevronDownIcon className="w-4 h-4" />
                      ) : (
                        <ChevronRightIcon className="w-4 h-4" />
                      )}
                    </Button>
                  )}
                </TableCell>
                <TableCell className="font-mono">{pod.proof}</TableCell>
                <TableCell>{pod.pod_class}</TableCell>
                <TableCell>
                  {pod.pod_class === "Signed" ? (
                    <div>
                      <div className="text-sm text-gray-500">
                        {Object.keys(pod.entries).length} key-value pairs
                      </div>
                    </div>
                  ) : (
                    <div>Main POD</div>
                  )}
                </TableCell>
                <TableCell>
                  <Button
                    variant="ghost"
                    size="icon"
                    onClick={() => handleDelete(pod.proof)}
                  >
                    <TrashIcon className="w-4 h-4" />
                  </Button>
                </TableCell>
              </TableRow>
              {pod.pod_class === "Signed" && expandedPods.has(pod.proof) && (
                <TableRow>
                  <TableCell colSpan={5}>
                    <div className="bg-gray-50 p-4 rounded-lg">
                      <div className="space-y-2">
                        {Object.entries(pod.entries)
                          .sort(([keyA], [keyB]) => keyA.localeCompare(keyB))
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
