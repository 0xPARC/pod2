import { createFileRoute } from "@tanstack/react-router";

export const Route = createFileRoute("/")({
  component: App,
});

function App() {
  return (
    <>
      <title>ZuKYC Issuer</title>
      <div className="flex flex-col items-center justify-center h-screen">
        <h1 className="text-2xl font-bold">ZuKYC Issuer</h1>
        <hr className="w-48 border-t-2 border-gray-300 my-4" />
        <div className="flex flex-col gap-4">
          <a href="/zoo-deel" className="text-blue-500 hover:underline">
            ZooDeel
          </a>
          <a href="/zoo-gov" className="text-blue-500 hover:underline">
            ZooGov
          </a>
        </div>
      </div>
    </>
  );
}
