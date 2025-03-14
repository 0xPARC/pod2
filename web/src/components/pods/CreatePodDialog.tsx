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
import { PlusIcon, TrashIcon } from "lucide-react";
import { Input } from "@/components/ui/input";
import {
  Select,
  SelectContent,
  SelectItem,
  SelectTrigger,
  SelectValue
} from "@/components/ui/select";

interface CreatePodDialogProps {
  onPodCreated: () => void;
}

type ValueType = "string" | "number";

interface KeyValuePair {
  key: string;
  type: ValueType;
  value: string;
}

export function CreatePodDialog({ onPodCreated }: CreatePodDialogProps) {
  const [open, setOpen] = useState(false);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [keyValuePairs, setKeyValuePairs] = useState<KeyValuePair[]>([
    { key: "", type: "string", value: "" }
  ]);

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

  async function handleCreateSignedPod() {
    try {
      setLoading(true);
      setError(null);

      // Convert key-value pairs to the format expected by the API
      const keyValues: Record<string, any> = {};
      for (const pair of keyValuePairs) {
        if (!pair.key) continue;
        keyValues[pair.key] =
          pair.type === "number" ? parseInt(pair.value, 10) : pair.value;
      }

      await api.createSignedPod("example-signer", keyValues);
      setOpen(false);
      onPodCreated();
    } catch (err) {
      setError("Failed to create Signed POD");
      console.error(err);
    } finally {
      setLoading(false);
    }
  }

  function addKeyValuePair() {
    setKeyValuePairs([
      ...keyValuePairs,
      { key: "", type: "string", value: "" }
    ]);
  }

  function removeKeyValuePair(index: number) {
    setKeyValuePairs(keyValuePairs.filter((_, i) => i !== index));
  }

  function updateKeyValuePair(
    index: number,
    field: keyof KeyValuePair,
    value: string
  ) {
    const newPairs = [...keyValuePairs];
    newPairs[index] = { ...newPairs[index], [field]: value };
    setKeyValuePairs(newPairs);
  }

  return (
    <Dialog open={open} onOpenChange={setOpen}>
      <DialogTrigger asChild>
        <Button>
          <PlusIcon className="w-4 h-4 mr-2" />
          New POD
        </Button>
      </DialogTrigger>
      <DialogContent className="max-w-2xl">
        <DialogHeader>
          <DialogTitle>Create New POD</DialogTitle>
          <DialogDescription>
            Choose the type of POD you want to create.
          </DialogDescription>
        </DialogHeader>
        <div className="grid gap-4 py-4">
          <Button
            onClick={handleCreateMainPod}
            disabled={loading}
            variant="outline"
          >
            Create Main POD
          </Button>

          <div className="space-y-4">
            <div className="flex items-center justify-between">
              <h3 className="text-sm font-medium">
                Signed POD Key-Value Pairs
              </h3>
              <Button
                type="button"
                variant="outline"
                size="sm"
                onClick={addKeyValuePair}
              >
                <PlusIcon className="w-4 h-4 mr-2" />
                Add Pair
              </Button>
            </div>

            {keyValuePairs.map((pair, index) => (
              <div key={index} className="flex items-center gap-2">
                <Input
                  placeholder="Key"
                  value={pair.key}
                  onChange={(e: React.ChangeEvent<HTMLInputElement>) =>
                    updateKeyValuePair(index, "key", e.target.value)
                  }
                  className="flex-1"
                />
                <Select
                  value={pair.type}
                  onValueChange={(value: ValueType) =>
                    updateKeyValuePair(index, "type", value)
                  }
                >
                  <SelectTrigger className="w-[120px]">
                    <SelectValue />
                  </SelectTrigger>
                  <SelectContent>
                    <SelectItem value="string">String</SelectItem>
                    <SelectItem value="number">Number</SelectItem>
                  </SelectContent>
                </Select>
                <Input
                  placeholder="Value"
                  value={pair.value}
                  onChange={(e: React.ChangeEvent<HTMLInputElement>) =>
                    updateKeyValuePair(index, "value", e.target.value)
                  }
                  className="flex-1"
                />
                <Button
                  type="button"
                  variant="ghost"
                  size="icon"
                  onClick={() => removeKeyValuePair(index)}
                >
                  <TrashIcon className="w-4 h-4" />
                </Button>
              </div>
            ))}

            <Button
              onClick={handleCreateSignedPod}
              disabled={
                loading ||
                keyValuePairs.some((pair) => !pair.key || !pair.value)
              }
            >
              Create Signed POD
            </Button>
          </div>

          {error && <p className="text-red-500 text-sm">{error}</p>}
        </div>
      </DialogContent>
    </Dialog>
  );
}
