import React from "react";
import { Card, CardContent, CardHeader, CardTitle, CardDescription } from "@/components/ui/card";
import { FileSignature, ClipboardCopy } from "lucide-react";
import type { SignedPod } from "@/types/pod2";
import ValueRenderer from "./ValueRenderer";
import { Button } from "./ui/button";
import { toast } from "sonner";

interface SignedPodCardProps {
  signedPod: SignedPod;
  podId?: string;
  label?: string | null;
}

const SignedPodCard: React.FC<SignedPodCardProps> = ({ signedPod, podId, label }) => {
  const handleExport = async () => {
    try {
      const jsonString = JSON.stringify(signedPod, null, 2);
      await navigator.clipboard.writeText(jsonString);
      toast.success("POD payload copied to clipboard.");
    } catch (err) {
      console.error("Failed to copy to clipboard:", err);
      toast.error("Failed to copy POD payload to clipboard.");
    }
  };

  return (
    <Card className="w-full mx-auto">
      <CardHeader>
        <div className="flex justify-between items-center">
          <CardTitle className="flex items-center">
            <span className="mr-2"><FileSignature className="w-4 h-4 text-teal-500 dark:text-teal-400" /></span> Signed POD Details
          </CardTitle>
          <Button variant="outline" size="sm" onClick={handleExport}>
            <ClipboardCopy className="w-4 h-4 mr-2" />
            Export
          </Button>
        </div>
        <CardDescription className="mt-2">
          {podId && <div>
            <span className="font-semibold">ID:</span> {podId}
          </div>}
          {label && <div>
            <span className="font-semibold">Label:</span> {label}
          </div>}
        </CardDescription>
      </CardHeader>
      <CardContent>
        <h4 className="font-semibold mb-2 text-sm text-muted-foreground">Entries:</h4>
        {Object.keys(signedPod.entries).length > 0 ? (
          <div className="border rounded-md">
            {Object.entries(signedPod.entries).sort((a, b) => a[0].localeCompare(b[0])).map(([key, value], index, arr) => (
              <div
                key={key}
                className={`flex p-2 text-sm ${index < arr.length - 1 ? 'border-b' : ''}`}
              >
                <div className="w-1/3 font-medium text-gray-700 dark:text-gray-300 break-all pr-2">{key}</div>
                <div className="w-2/3 text-gray-900 dark:text-gray-100 break-all">
                  <ValueRenderer value={value} />
                </div>
              </div>
            ))}
          </div>
        ) : (
          <p className="text-sm text-muted-foreground italic">No entries in this POD.</p>
        )}
        {/* Display more SignedPod specific details here, e.g., proof */}
      </CardContent>
    </Card>
  );
};

export default SignedPodCard; 