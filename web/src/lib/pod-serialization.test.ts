import { describe, it, expect } from "vitest";
import { numberToString, serializePodTree } from "./pod-serialization";
import type { TreeNode } from "@/components/pods/CreateSignedPodEditor";

describe("pod-serialization", () => {
  describe("numberToString", () => {
    it("should handle regular integers", () => {
      expect(numberToString(42)).toBe("42");
      expect(numberToString(-42)).toBe("-42");
      expect(numberToString(0)).toBe("0");
    });

    it("should handle large integers within i64 bounds", () => {
      expect(numberToString("9223372036854775807")).toBe("9223372036854775807");
      expect(numberToString("-9223372036854775808")).toBe(
        "-9223372036854775808"
      );
    });

    it("should throw error for integers above i64 max", () => {
      expect(() => numberToString("9223372036854775808")).toThrow(
        "Integer value 9223372036854775808 is outside of i64 bounds"
      );
    });

    it("should throw error for integers below i64 min", () => {
      expect(() => numberToString("-9223372036854775809")).toThrow(
        "Integer value -9223372036854775809 is outside of i64 bounds"
      );
    });

    it("should throw error for invalid number formats", () => {
      expect(() => numberToString("not a number")).toThrow(
        "Invalid integer value: not a number"
      );
      expect(() => numberToString("1.5")).toThrow("Invalid integer value: 1.5");
    });
  });

  describe("serializePodTree", () => {
    it("should serialize a simple integer node", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "test",
          type: "integer",
          value: "42"
        }
      ];

      const result = serializePodTree(nodes);
      expect(result).toEqual({
        signer: "example-signer",
        key_values: {
          test: { Int: "42" }
        }
      });
    });

    it("should serialize a large integer within bounds", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "test",
          type: "integer",
          value: "9223372036854775807"
        }
      ];

      const result = serializePodTree(nodes);
      expect(result).toEqual({
        signer: "example-signer",
        key_values: {
          test: { Int: "9223372036854775807" }
        }
      });
    });

    it("should throw error when serializing integer outside bounds", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "test",
          type: "integer",
          value: "9223372036854775808"
        }
      ];

      expect(() => serializePodTree(nodes)).toThrow(
        "Integer value 9223372036854775808 is outside of i64 bounds"
      );
    });

    it("should serialize nested integer values in arrays", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "test",
          type: "array",
          value: [],
          children: [
            {
              id: "2",
              key: "",
              type: "integer",
              value: "42"
            }
          ]
        }
      ];

      const result = serializePodTree(nodes);
      expect(result).toEqual({
        signer: "example-signer",
        key_values: {
          test: [{ Int: "42" }]
        }
      });
    });

    it("should serialize nested integer values in dictionaries", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "test",
          type: "dictionary",
          value: {},
          children: [
            {
              id: "2",
              key: "nested",
              type: "integer",
              value: "42"
            }
          ]
        }
      ];

      const result = serializePodTree(nodes);
      expect(result).toEqual({
        signer: "example-signer",
        key_values: {
          test: {
            Dictionary: {
              nested: { Int: "42" }
            }
          }
        }
      });
    });
  });
});
