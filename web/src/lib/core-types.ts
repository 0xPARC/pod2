import { z } from "zod";

// Core value types
export type PODValue =
  | { Raw: string }
  | { Int: string }
  | { Set: PODValue[] }
  | { Dictionary: Record<string, PODValue> }
  | PODValue[]
  | string
  | boolean;

export const ValueSchema: z.ZodType<PODValue> = z.union([
  z.string(),
  z.boolean(),
  z.array(z.lazy(() => ValueSchema)),
  z.object({
    Raw: z.string().regex(/^[0-9a-fA-F]{64}$/)
  }),
  z.object({
    Int: z.string()
  }),
  z.object({
    Set: z.array(z.lazy(() => ValueSchema))
  }),
  z.object({
    Dictionary: z.record(
      z.string(),
      z.lazy(() => ValueSchema)
    )
  })
]);

// Statement types
export const OriginSchema = z.object({
  pod_class: z.enum(["Signed", "Main"]),
  pod_id: z.string().regex(/^[0-9a-fA-F]{64}$/)
});

export const AnchoredKeySchema = z.object({
  origin: OriginSchema,
  key: z.string()
});

export const StatementArgSchema = z.union([
  z.object({
    Key: AnchoredKeySchema
  }),
  z.object({
    Literal: ValueSchema
  })
]);

export const NativePredicateSchema = z.enum([
  "None",
  "ValueOf",
  "Equal",
  "NotEqual",
  "Gt",
  "Lt",
  "Contains",
  "NotContains",
  "SumOf",
  "ProductOf",
  "MaxOf"
]);

export type NativePredicateValue = z.infer<typeof NativePredicateSchema>;

export const PredicateSchema = z.discriminatedUnion("type", [
  z.object({
    type: z.literal("Native"),
    value: NativePredicateSchema
  }),
  z.object({
    type: z.literal("BatchSelf"),
    value: z.number().int().nonnegative()
  }),
  z.object({
    type: z.literal("Custom"),
    value: z.tuple([
      z.object({
        name: z.string(),
        predicates: z.array(
          z.object({
            conjunction: z.boolean(),
            statements: z.array(
              z.tuple([
                z.any(), // Predicate
                z.array(z.any()) // StatementTmplArg array
              ])
            ),
            args_len: z.number().int().nonnegative()
          })
        )
      }),
      z.number().int().nonnegative()
    ])
  })
]);

export const StatementSchema = z.object({
  predicate: PredicateSchema,
  args: z.array(StatementArgSchema)
});

// Types derived from schemas
export type Origin = z.infer<typeof OriginSchema>;
export type AnchoredKey = z.infer<typeof AnchoredKeySchema>;
export type StatementArg = z.infer<typeof StatementArgSchema>;
export type Predicate = z.infer<typeof PredicateSchema>;
export type Statement = z.infer<typeof StatementSchema>;

// Helper functions
export function shortenId(id: string): string {
  return id.slice(0, 6);
}

export function formatValue(value: PODValue): string {
  if (typeof value === "string") return value;
  if (typeof value === "boolean") return String(value);
  if ("Int" in value) return value.Int;
  if ("Raw" in value) return `Raw:${shortenId(value.Raw)}`;
  if ("Set" in value) return `Set(${value.Set.length} items)`;
  if ("Dictionary" in value)
    return `Dict(${Object.keys(value.Dictionary).length} items)`;
  if (Array.isArray(value)) return `Array(${value.length} items)`;
  return "";
}

export function formatAnchoredKey(key: AnchoredKey): string {
  return `${key.origin.pod_class}:${shortenId(key.origin.pod_id)}.${key.key}`;
}

export function formatArg(arg: StatementArg): string {
  if ("Key" in arg) {
    return formatAnchoredKey(arg.Key);
  } else if ("Literal" in arg) {
    return formatValue(arg.Literal);
  }
  return "";
}

export function formatStatement(statement: Statement): string {
  const { predicate, args } = statement;
  if (predicate.type !== "Native") return "";

  // Special handling for ValueOf which typically has one argument
  if (predicate.value === "ValueOf" && args.length > 0) {
    return `${predicate.value}(${formatArg(args[0])})`;
  }

  // For other predicates that typically have two arguments
  const formattedArgs = args.map(formatArg).filter((arg) => arg !== "");
  return `${predicate.value}(${formattedArgs.join(", ")})`;
}

// Validation functions
export const validateStatement = (data: unknown): Statement => {
  return StatementSchema.parse(data);
};

export const validateStatements = (data: unknown): Statement[] => {
  return z.array(StatementSchema).parse(data);
};
