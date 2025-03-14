import { useState } from "react";
import { api } from "@/lib/api";
import {
  Dialog,
  DialogContent,
  DialogDescription,
  DialogHeader,
  DialogTitle,
  DialogTrigger
} from "@/components/ui/dialog";
import { Button } from "@/components/ui/button";
import { PlusIcon } from "lucide-react";

interface CreateMainPodDialogProps {
  onPodCreated: () => void;
}

export function CreateMainPodDialog({
  onPodCreated
}: CreateMainPodDialogProps) {
  const [open, setOpen] = useState(false);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  async function handleCreateMainPod() {
    try {
      setLoading(true);
      setError(null);
      await api.createMainPod();
      setOpen(false);
      onPodCreated();
    } catch (err) {
      setError("Failed to create Main POD");
      console.error(err);
    } finally {
      setLoading(false);
    }
  }

  return (
    <Dialog open={open} onOpenChange={setOpen}>
      <DialogTrigger asChild>
        <Button variant="outline">
          <PlusIcon className="w-4 h-4 mr-2" />
          Create Main POD
        </Button>
      </DialogTrigger>
      <DialogContent>
        <DialogHeader>
          <DialogTitle>Create Main POD</DialogTitle>
          <DialogDescription>
            Create a new Main POD that can contain public statements.
          </DialogDescription>
        </DialogHeader>
        <div className="grid gap-4 py-4">
          <Button onClick={handleCreateMainPod} disabled={loading}>
            Create Main POD
          </Button>
          {error && <p className="text-red-500 text-sm">{error}</p>}
        </div>
      </DialogContent>
    </Dialog>
  );
}
