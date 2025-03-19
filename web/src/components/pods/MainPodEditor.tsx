/* eslint-disable @typescript-eslint/no-unused-vars */
import { useState } from "react";
import { useNavigate } from "@tanstack/react-router";
import { Button } from "@/components/ui/button";
import { Input } from "@/components/ui/input";
import {
  Select,
  SelectContent,
  SelectItem,
  SelectTrigger,
  SelectValue
} from "@/components/ui/select";
import { Plus, Trash2 } from "lucide-react";
import { toast } from "sonner";
import { Statement } from "@/lib/api";
import { ValueType } from "@/lib/types";
import { SerializedValue } from "@/lib/pod-serialization";

function generateId() {
  return crypto.randomUUID();
}

type NativePredicateValue =
  | "None"
  | "ValueOf"
  | "Equal"
  | "NotEqual"
  | "Gt"
  | "Lt"
  | "Contains"
  | "NotContains"
  | "SumOf"
  | "ProductOf"
  | "MaxOf";

function ArgumentEditor({
  value,
  onChange,
  onDelete
}: {
  value: Statement["args"][0];
  onChange: (value: Statement["args"][0]) => void;
  onDelete: () => void;
}) {
  const [argType, setArgType] = useState<"Key" | "Literal">(
    "Key" in value ? "Key" : "Literal"
  );

  const getLiteralType = (value: Statement["args"][0]): ValueType => {
    if ("Literal" in value) {
      const literal = value.Literal;
      if (typeof literal === "string") return ValueType.String;
      if (typeof literal === "boolean") return ValueType.Bool;
      if (typeof literal === "object") {
        if ("Int" in literal) return ValueType.Int;
        if ("Set" in literal) return ValueType.Set;
        if ("Dictionary" in literal) return ValueType.Dictionary;
        if (Array.isArray(literal)) return ValueType.Array;
      }
    }
    return ValueType.String;
  };

  const getLiteralValue = (value: Statement["args"][0]): string => {
    if ("Literal" in value) {
      const literal = value.Literal;
      if (typeof literal === "string") return literal;
      if (typeof literal === "boolean") return String(literal);
      if (typeof literal === "object") {
        if ("Int" in literal) return literal.Int;
        if ("Set" in literal) return JSON.stringify(literal.Set);
        if ("Dictionary" in literal) return JSON.stringify(literal.Dictionary);
        if (Array.isArray(literal)) return JSON.stringify(literal);
      }
    }
    return "";
  };

  const [literalType, setLiteralType] = useState<ValueType>(
    getLiteralType(value)
  );
  const [literalValue, setLiteralValue] = useState<string>(
    getLiteralValue(value)
  );

  function handleArgTypeChange(type: "Key" | "Literal") {
    setArgType(type);
    if (type === "Key") {
      onChange({
        Key: { origin: { pod_class: "Signed", pod_id: "" }, key: "" }
      });
    } else {
      onChange({ Literal: "" });
    }
  }

  function handleLiteralTypeChange(type: ValueType) {
    setLiteralType(type);
    setLiteralValue("");
    let defaultValue: SerializedValue;
    switch (type) {
      case ValueType.Bool:
        defaultValue = false;
        break;
      case ValueType.Array:
        defaultValue = [];
        break;
      case ValueType.Set:
        defaultValue = { Set: [] };
        break;
      case ValueType.Dictionary:
        defaultValue = { Dictionary: {} };
        break;
      default:
        defaultValue = "";
    }
    onChange({ Literal: defaultValue });
  }

  function handleLiteralValueChange(value: string) {
    setLiteralValue(value);
    let parsedValue: SerializedValue;
    try {
      switch (literalType) {
        case ValueType.Bool:
          parsedValue = value === "true";
          break;
        case ValueType.Int:
          parsedValue = { Int: value };
          break;
        case ValueType.Array:
          parsedValue = JSON.parse(value);
          break;
        case ValueType.Set:
          parsedValue = { Set: JSON.parse(value) };
          break;
        case ValueType.Dictionary:
          parsedValue = { Dictionary: JSON.parse(value) };
          break;
        default:
          parsedValue = value;
      }
      onChange({ Literal: parsedValue });
    } catch (err) {
      toast.error("Invalid JSON format");
    }
  }

  return (
    <div className="flex items-center gap-2">
      <Select value={argType} onValueChange={handleArgTypeChange}>
        <SelectTrigger className="w-32">
          <SelectValue />
        </SelectTrigger>
        <SelectContent>
          <SelectItem value="Key">Anchored Key</SelectItem>
          <SelectItem value="Literal">Literal</SelectItem>
        </SelectContent>
      </Select>

      {argType === "Literal" && (
        <>
          <Select value={literalType} onValueChange={handleLiteralTypeChange}>
            <SelectTrigger className="w-32">
              <SelectValue />
            </SelectTrigger>
            <SelectContent>
              <SelectItem value={ValueType.String}>String</SelectItem>
              <SelectItem value={ValueType.Int}>Integer</SelectItem>
              <SelectItem value={ValueType.Bool}>Boolean</SelectItem>
              <SelectItem value={ValueType.Array}>Array</SelectItem>
              <SelectItem value={ValueType.Set}>Set</SelectItem>
              <SelectItem value={ValueType.Dictionary}>Dictionary</SelectItem>
            </SelectContent>
          </Select>

          {literalType === ValueType.Bool ? (
            <Select
              value={String(literalValue)}
              onValueChange={handleLiteralValueChange}
            >
              <SelectTrigger className="w-32">
                <SelectValue />
              </SelectTrigger>
              <SelectContent>
                <SelectItem value="true">True</SelectItem>
                <SelectItem value="false">False</SelectItem>
              </SelectContent>
            </Select>
          ) : (
            <Input
              placeholder={
                literalType === ValueType.Int
                  ? "Integer (i64)"
                  : literalType === ValueType.Array ||
                      literalType === ValueType.Set ||
                      literalType === ValueType.Dictionary
                    ? "JSON format"
                    : "Value"
              }
              value={literalValue}
              onChange={(e) => handleLiteralValueChange(e.target.value)}
              className="w-48"
              type={literalType === ValueType.Int ? "text" : "text"}
            />
          )}
        </>
      )}

      {argType === "Key" && (
        <div className="text-muted-foreground">
          Anchored Key editor placeholder
        </div>
      )}

      <Button
        variant="ghost"
        size="icon"
        onClick={onDelete}
        aria-label="Delete"
      >
        <Trash2 className="h-4 w-4" />
      </Button>
    </div>
  );
}

export function StatementEditor({
  statement,
  onUpdate,
  onDelete,
  onAddArg
}: {
  statement: Statement;
  onUpdate: (statement: Statement) => void;
  onDelete: () => void;
  onAddArg: () => void;
}) {
  function handlePredicateChange(value: NativePredicateValue) {
    onUpdate({
      ...statement,
      predicate: {
        type: "Native",
        value
      },
      args: []
    });
  }

  function handleArgChange(index: number, value: Statement["args"][0]) {
    const newArgs = [...statement.args];
    newArgs[index] = value;
    onUpdate({ ...statement, args: newArgs });
  }

  function handleArgDelete(index: number) {
    const newArgs = statement.args.filter((_, i) => i !== index);
    onUpdate({ ...statement, args: newArgs });
  }

  const needsThreeArgs = ["SumOf", "ProductOf", "MaxOf"].includes(
    statement.predicate.type === "Native" ? statement.predicate.value : ""
  );

  return (
    <div className="flex flex-col gap-2 py-2">
      <div className="flex items-center gap-2">
        <Select
          value={
            statement.predicate.type === "Native"
              ? statement.predicate.value
              : "Custom"
          }
          onValueChange={handlePredicateChange}
        >
          <SelectTrigger className="w-32">
            <SelectValue />
          </SelectTrigger>
          <SelectContent>
            <SelectItem value="None">None</SelectItem>
            <SelectItem value="ValueOf">Value Of</SelectItem>
            <SelectItem value="Equal">Equal</SelectItem>
            <SelectItem value="NotEqual">Not Equal</SelectItem>
            <SelectItem value="Gt">Greater Than</SelectItem>
            <SelectItem value="Lt">Less Than</SelectItem>
            <SelectItem value="Contains">Contains</SelectItem>
            <SelectItem value="NotContains">Not Contains</SelectItem>
            <SelectItem value="SumOf">Sum Of</SelectItem>
            <SelectItem value="ProductOf">Product Of</SelectItem>
            <SelectItem value="MaxOf">Max Of</SelectItem>
          </SelectContent>
        </Select>

        <Button
          variant="ghost"
          size="icon"
          onClick={onDelete}
          aria-label="Delete"
        >
          <Trash2 className="h-4 w-4" />
        </Button>
      </div>

      <div className="space-y-2 pl-4">
        {statement.args.map((arg, index) => (
          <ArgumentEditor
            key={index}
            value={arg}
            onChange={(value) => handleArgChange(index, value)}
            onDelete={() => handleArgDelete(index)}
          />
        ))}
        {statement.args.length < (needsThreeArgs ? 3 : 2) && (
          <Button variant="outline" size="sm" onClick={onAddArg}>
            <Plus className="h-4 w-4 mr-2" />
            Add Argument
          </Button>
        )}
      </div>
    </div>
  );
}

export function MainPodEditor() {
  const navigate = useNavigate();
  const [statements, setStatements] = useState<Statement[]>([]);
  const [nickname, setNickname] = useState<string>("");

  async function handleCreatePod() {
    try {
      // TODO: Implement MainPod creation
      toast.success("Main POD created successfully");
      navigate({ to: "/" });
    } catch (err) {
      console.error("Failed to create Main POD:", err);
      toast.error("Failed to create Main POD");
    }
  }

  function addStatement() {
    const newStatement: Statement = {
      predicate: {
        type: "Native",
        value: "None"
      },
      args: []
    };
    setStatements([...statements, newStatement]);
  }

  return (
    <div className="container mx-auto py-8">
      <div className="flex justify-between items-center mb-6">
        <h1 className="text-2xl font-bold">Create Main POD</h1>
        <div className="space-x-2">
          <Button variant="outline" onClick={() => navigate({ to: "/" })}>
            Cancel
          </Button>
          <Button onClick={handleCreatePod}>Create POD</Button>
        </div>
      </div>

      <div className="bg-white rounded-lg shadow p-6">
        <div className="space-y-4">
          <div className="space-y-2">
            <label htmlFor="nickname" className="text-sm font-medium">
              Nickname (optional)
            </label>
            <Input
              id="nickname"
              placeholder="Enter a nickname for this POD"
              value={nickname}
              onChange={(e) => setNickname(e.target.value)}
              className="w-full"
            />
          </div>

          <div className="space-y-2">
            {statements.length === 0 ? (
              <div className="text-center text-muted-foreground py-8">
                No statements added yet. Click "Add Statement" to begin.
              </div>
            ) : (
              statements.map((statement) => (
                <StatementEditor
                  key={generateId()}
                  statement={statement}
                  onUpdate={(updatedStatement) => {
                    setStatements(
                      statements.map((s) =>
                        s === statement ? updatedStatement : s
                      )
                    );
                  }}
                  onDelete={() => {
                    setStatements(statements.filter((s) => s !== statement));
                  }}
                  onAddArg={() => {
                    // TODO: Implement adding arguments to statements
                  }}
                />
              ))
            )}
            <div className="flex justify-center">
              <Button variant="outline" onClick={addStatement}>
                <Plus className="h-4 w-4 mr-2" />
                Add Statement
              </Button>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}
