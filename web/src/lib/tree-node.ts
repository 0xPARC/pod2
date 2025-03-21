import { PODValue } from "./core-types";

export enum ValueType {
  String = "String",
  Int = "Int",
  Bool = "Bool",
  Array = "Array",
  Set = "Set",
  Dictionary = "Dictionary",
  Raw = "Raw"
}

export interface TreeNode {
  id: string;
  key: string;
  type: ValueType;
  value: PODValue;
  children?: TreeNode[];
}

export function isCollectionType(type: ValueType): boolean {
  return (
    type === ValueType.Array ||
    type === ValueType.Set ||
    type === ValueType.Dictionary
  );
}

export function transformNodeToValue(node: TreeNode): PODValue {
  if (node.type === ValueType.Array) {
    return node.children?.map((child) => transformNodeToValue(child)) ?? [];
  }
  if (node.type === ValueType.Set) {
    return {
      Set: node.children?.map((child) => transformNodeToValue(child)) ?? []
    };
  }
  if (node.type === ValueType.Dictionary) {
    return {
      Dictionary: Object.fromEntries(
        node.children?.map((child) => [
          child.key,
          transformNodeToValue(child)
        ]) ?? []
      )
    };
  }
  return node.value; // For primitive types
}
