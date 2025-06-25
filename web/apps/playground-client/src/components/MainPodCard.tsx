import React from "react";
import type { MainPod, ValueRef } from "@/types/pod2";
import ValueRenderer from "./ValueRenderer";
import { FileCheck2, ClipboardCopy } from "lucide-react";
import { Card, CardHeader, CardTitle, CardDescription, CardContent } from "./ui/card";
import { Button } from "./ui/button";
import { toast } from "sonner";

interface MainPodCardProps {
  mainPod: MainPod;
  podId?: string;
  label?: string | null;
  // onClick?: () => void; // For future "open in tab" functionality
}

// function isAnchoredKey(arg: AnchoredKey | Value): arg is AnchoredKey {
//   return typeof arg === 'object' && 'key' in arg;
// }

function ViewStatementArg({ arg }: { arg: ValueRef }) {
  if (arg.type === "Key") {
    return <span>{arg.value.podId}["{arg.value.key}"]</span>;
  }
  return <ValueRenderer value={arg.value} />;
}

const MainPodCard: React.FC<MainPodCardProps> = ({ mainPod, podId, label }) => {
  const statementCount = mainPod.publicStatements?.length || 0;

  const handleExport = async () => {
    try {
      const jsonString = JSON.stringify(mainPod, null, 2);
      await navigator.clipboard.writeText(jsonString);
      toast.success("POD payload copied to clipboard.");
    } catch (err) {
      console.error("Failed to copy to clipboard:", err);
      toast.error("Failed to copy POD payload to clipboard.");
    }
  };

  // Placeholder icon, can be replaced with an SVG or icon library component

  return (
    <Card className="w-full mx-auto">
      <CardHeader>
        <div className="flex justify-between items-center">
          <CardTitle className="flex items-center">
            <span className="mr-2"><FileCheck2 className="w-4 h-4 text-sky-500 dark:text-sky-400" /></span> Main POD Details
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
        <h4 className="font-semibold mb-2 text-sm text-muted-foreground">Statements:</h4>
        {statementCount > 0 ? (
          <div className="border rounded-md">
            {mainPod.publicStatements?.map((statement, index, arr) => (
              <div
                key={index}
                className={`flex p-2 text-sm ${index < arr.length - 1 ? 'border-b' : ''}`}
              >
                <div className="w-1/3 font-medium text-gray-700 dark:text-gray-300 break-all pr-2">{statement.predicate}</div>
                <div className="w-2/3 text-gray-900 dark:text-gray-100 break-all">
                  {statement.predicate !== "Custom" && statement.predicate !== "None" && statement.args.map((arg, index) => (
                    <div key={index} className="flex items-center">
                      <ViewStatementArg key={index} arg={arg} />
                    </div>
                  ))}
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

export default MainPodCard;
