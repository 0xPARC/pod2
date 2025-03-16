import { TreeNode } from "@/components/pods/CreateSignedPodEditor";

// Types for the serialized POD format
type RawValue = { Raw: string };
type IntValue = { Int: string };
type SetValue = { Set: [string[], string] };
type DictionaryValue = { Dictionary: Record<string, SerializedValue> };
type ArrayValue = SerializedValue[];

type SerializedValue =
  | RawValue
  | IntValue
  | SetValue
  | DictionaryValue
  | ArrayValue
  | string;

// Constants for i64 limits in Rust
const I64_MIN = -9223372036854775808n;
const I64_MAX = 9223372036854775807n;

// Helper function to convert a number to a string representation
// This handles large integers that need to be preserved exactly
// Throws an error if the number is outside i64 bounds
export function numberToString(n: number | string): string {
  try {
    // Convert to BigInt to preserve precision
    const bigIntValue =
      typeof n === "string" ? BigInt(n) : BigInt(Math.floor(n));

    // Validate against i64 bounds
    if (bigIntValue < I64_MIN || bigIntValue > I64_MAX) {
      throw new Error(`Integer value ${bigIntValue} is outside of i64 bounds`);
    }

    return bigIntValue.toString();
  } catch (err) {
    if (err instanceof Error && err.message.includes("i64 bounds")) {
      throw err;
    }
    throw new Error(`Invalid integer value: ${n}`);
  }
}

// Convert a value to its serialized format
function serializeValue(node: TreeNode): any {
  switch (node.type) {
    case "string":
      return node.value as string;

    case "integer":
      return { Int: numberToString(node.value as string) };

    case "boolean":
      return { Raw: (node.value as boolean).toString() };

    case "array":
      return (node.children || []).map((child: TreeNode) =>
        serializeValue(child)
      );

    case "set":
      const setValue = node.value as Set<string | number>;
      const arrayValue = Array.from(setValue).map(String);
      return { Set: [arrayValue, arrayValue[0] || ""] };

    case "dictionary":
      const dict: Record<string, any> = {};
      node.children?.forEach((child: TreeNode) => {
        dict[child.key] = serializeValue(child);
      });
      return { Dictionary: dict };

    default:
      throw new Error(`Unsupported node type: ${node.type}`);
  }
}

// Convert the tree editor state to a CreateSignedPodRequest format
export function serializePodTree(rootNodes: TreeNode[]): {
  signer: string;
  key_values: Record<string, any>;
} {
  const key_values: Record<string, any> = {};

  // Add all root nodes to the key_values
  rootNodes.forEach((node) => {
    key_values[node.key] = serializeValue(node);
  });

  return {
    signer: "example-signer", // TODO: Make this configurable
    key_values
  };
}
