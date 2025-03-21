import { useState } from "react";
import { Input } from "@/components/ui/input";
import { Button } from "@/components/ui/button";
import { CheckIcon, XIcon } from "lucide-react";
import { api } from "@/lib/api";
import { toast } from "sonner";

interface EditableNicknameProps {
  id: string;
  initialNickname: string | null | undefined;
  onUpdate: () => void;
}

export function EditableNickname({
  id,
  initialNickname,
  onUpdate
}: EditableNicknameProps) {
  const [isEditing, setIsEditing] = useState(false);
  const [nickname, setNickname] = useState(initialNickname || "");

  const handleSubmit = async () => {
    try {
      await api.updatePodNickname(id, nickname || null);
      setIsEditing(false);
      onUpdate();
      toast.success("Nickname updated successfully");
    } catch (error) {
      console.error("Failed to update nickname:", error);
      toast.error("Failed to update nickname");
    }
  };

  const handleCancel = () => {
    setNickname(initialNickname || "");
    setIsEditing(false);
  };

  if (isEditing) {
    return (
      <div className="flex items-center space-x-2">
        <Input
          value={nickname}
          onChange={(e) => setNickname(e.target.value)}
          placeholder="Enter nickname"
          className="h-8 w-[200px]"
          autoFocus
        />
        <Button
          variant="ghost"
          size="icon"
          className="h-8 w-8"
          onClick={handleSubmit}
        >
          <CheckIcon className="h-4 w-4" />
        </Button>
        <Button
          variant="ghost"
          size="icon"
          className="h-8 w-8"
          onClick={handleCancel}
        >
          <XIcon className="h-4 w-4" />
        </Button>
      </div>
    );
  }

  return (
    <div
      className="cursor-pointer hover:bg-gray-100 rounded px-2 py-1"
      onClick={() => setIsEditing(true)}
    >
      {initialNickname || (
        <span className="text-gray-400 italic">No nickname</span>
      )}
    </div>
  );
}
