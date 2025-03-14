import { useState } from "react";
import { api, Pod } from "@/lib/api";
import {
  Dialog,
  DialogContent,
  DialogDescription,
  DialogHeader,
  DialogTitle,
  DialogTrigger
} from "@/components/ui/dialog";
import { Button } from "@/components/ui/button";
import { ImportIcon } from "lucide-react";

interface ImportPodDialogProps {
  onPodImported: () => void;
}

export function ImportPodDialog({ onPodImported }: ImportPodDialogProps) {
  const [open, setOpen] = useState(false);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [jsonInput, setJsonInput] = useState("");

  async function handleImport() {
    try {
      setLoading(true);
      setError(null);

      let podData: Pod;
      try {
        podData = JSON.parse(jsonInput);
      } catch (err) {
        setError("Invalid JSON format");
        return;
      }

      // Basic validation
      if (!podData.id) {
        setError("POD must have an ID");
        return;
      }

      await api.importPod(podData);
      setOpen(false);
      setJsonInput("");
      onPodImported();
    } catch (err) {
      setError("Failed to import POD");
      console.error(err);
    } finally {
      setLoading(false);
    }
  }

  return (
    <Dialog open={open} onOpenChange={setOpen}>
      <DialogTrigger asChild>
        <Button variant="outline">
          <ImportIcon className="w-4 h-4 mr-2" />
          Import POD
        </Button>
      </DialogTrigger>
      <DialogContent>
        <DialogHeader>
          <DialogTitle>Import POD</DialogTitle>
          <DialogDescription>
            Paste the POD JSON data below to import it.
          </DialogDescription>
        </DialogHeader>
        <div className="grid gap-4 py-4">
          <textarea
            className="min-h-[200px] w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"
            placeholder='{"id": "...", "signer": "...", "keyValues": {...}}'
            value={jsonInput}
            onChange={(e) => setJsonInput(e.target.value)}
            disabled={loading}
          />
          <Button
            onClick={handleImport}
            disabled={loading || !jsonInput.trim()}
          >
            Import
          </Button>
          {error && <p className="text-red-500 text-sm">{error}</p>}
        </div>
      </DialogContent>
    </Dialog>
  );
}
