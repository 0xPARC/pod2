import {
  createRootRoute,
  createRoute,
  createRouter,
  Outlet
} from "@tanstack/react-router";
import { PodList } from "./components/pods/PodList";
import { MainPodEditor } from "./components/pods/MainPodEditor";
import { CreateSignedPodEditor } from "./components/pods/CreateSignedPodEditor";
import { Navigation } from "./components/layout/Navigation";
import { api } from "./lib/api";

// Root route
const rootRoute = createRootRoute({
  component: () => (
    <div className="min-h-screen bg-background">
      <Navigation />
      <main>
        <Outlet />
      </main>
    </div>
  )
});

// List route
const listRoute = createRoute({
  getParentRoute: () => rootRoute,
  path: "/",
  component: PodList,
  loader: async () => {
    const pods = await api.listPods();
    return { pods };
  }
});

// Create Main POD route
const createMainRoute = createRoute({
  getParentRoute: () => rootRoute,
  path: "/create/main",
  component: MainPodEditor
});

// Create Signed POD route
const createSignedRoute = createRoute({
  getParentRoute: () => rootRoute,
  path: "/create/signed",
  component: CreateSignedPodEditor
});

// Create the route tree
const routeTree = rootRoute.addChildren([
  listRoute,
  createMainRoute,
  createSignedRoute
]);

// Create the router
export const router = createRouter({ routeTree });

// Register the router for type safety
declare module "@tanstack/react-router" {
  interface Register {
    router: typeof router;
  }
}
